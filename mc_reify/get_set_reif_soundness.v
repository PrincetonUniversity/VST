Require Import  Coq.Numbers.BinNums.
Require Import compcert.lib.Maps.
Require Import mc_reify.func_defs.
Require Import mc_reify.get_set_reif.
Require Import mc_reify.app_lemmas.

Section tbled.

Parameter tbl : SymEnv.functions RType_typ.

Let RSym_sym := RSym_sym tbl.
Existing Instance RSym_sym.

Let RSym_sym_ok :  RSymOk RSym_sym := _.
Existing Instance RSym_sym_ok.


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


Lemma set_denote : forall i typ tus tvs,
exists v,
exprD' tus tvs (tyArr typ (tyArr (typtree typ) (typtree typ)))
     (Inj (inr (Data (fset typ i)))) = Some v.
Proof.
Admitted. (*works but takes foooreeverrr
intros.
simpl. induction typ; 
cbv [exprD' funcAs typeof_sym RSym_sym func_defs.RSym_sym  SymSum.RSym_sum RSym_Func' typeof_func_opt type_cast typeof_func typeof_data RType_typ];
match goal with 
| [ |- exists v,
         match 
           match 
             match typ_eq_dec ?a ?b 
             with _ => _ end
           with _ => _ end
         with _ => _ end = _]
                                   => destruct (typ_eq_dec a b); try congruence
end;
assert (e = eq_refl) by apply msl.Axioms.proof_irr; subst; 
try solve [eexists; reflexivity].
Qed. *)

Lemma exprD'_App_R_typ  e1 e2 tus tvs ty1 ty2 v:
exprD' tus tvs ty2 (App e1 e2) = Some v ->
typeof_expr tus tvs e2 = Some ty1 ->
(exists v1 , exprD' tus tvs (tyArr ty1 ty2) e1 = Some v1) /\ 
(exists v2, exprD' tus tvs ty1 e2 = Some v2).
Proof.
intros.
assert (X := @exprD'_typeof_expr typ _ _ _ _ _ _ _ tus (App e1 e2) tvs
ty2 v). assert (H2 : typeof_expr tus tvs (App e1 e2) = Some ty2).
apply X. intuition. clear X.
change (App e1 e2) with (AppN.apps e1 (e2 :: nil)) in *.
rewrite AppN.typeof_expr_apps in H2; auto with typeclass_instances.
unfold AppN.typeof_apps in H2. 
destruct (typeof_expr tus tvs e1) eqn:?; try congruence.
simpl in H2. destruct (typeof_expr tus tvs e2) eqn:?; try congruence.
simpl. destruct t; simpl in H2; try congruence.
destruct (typ_eq_dec t0 t1) eqn : ?; try congruence. 
inversion H2; subst; clear H2. 
inversion H0; subst; clear H0.
simpl in H.
change (App e1 e2) with (AppN.apps e1 (e2 :: nil)) in *.
clear Heqs. 
rewrite AppN.exprD'_apps in H; auto with typeclass_instances.
unfold AppN.apps_sem' in H. 
destruct (typeof_expr tus tvs e1) eqn:?; try congruence.
destruct (exprD' tus tvs t e1) eqn :?; try congruence.
inversion Heqo; subst; clear Heqo. split. eexists. apply Heqo2.
simpl in H. 
destruct (exprD' tus tvs ty1 e2) eqn:?; try congruence.
eexists; eauto.
Qed.

Lemma exprD'_App_L_typ  e1 e2 tus tvs ty1 ty2 v:
exprD' tus tvs ty2 (App e1 e2) = Some v ->
typeof_expr tus tvs e1 = Some (tyArr ty1 ty2) ->
(exists v1 , exprD' tus tvs (tyArr ty1 ty2) e1 = Some v1) /\ 
(exists v2, exprD' tus tvs ty1 e2 = Some v2).
Proof.
intros.
assert (X := @exprD'_typeof_expr typ _ _ _ _ _ _ _ tus (App e1 e2) tvs
ty2 v). assert (H2 : typeof_expr tus tvs (App e1 e2) = Some ty2).
apply X. intuition. clear X.
change (App e1 e2) with (AppN.apps e1 (e2 :: nil)) in *.
rewrite AppN.typeof_expr_apps in H2; auto with typeclass_instances.
unfold AppN.typeof_apps in H2. 
destruct (typeof_expr tus tvs e1) eqn:?; try congruence.
simpl in H2. destruct (typeof_expr tus tvs e2) eqn:?; try congruence.
simpl. destruct t; simpl in H2; try congruence.
destruct (typ_eq_dec t0 t1) eqn : ?; try congruence. 
inversion H2; subst; clear H2. 
inversion H0; subst; clear H0.
simpl in H.
change (App e1 e2) with (AppN.apps e1 (e2 :: nil)) in *.
clear Heqs. 
rewrite AppN.exprD'_apps in H; auto with typeclass_instances.
unfold AppN.apps_sem' in H. 
destruct (typeof_expr tus tvs e1) eqn:?; try congruence.
destruct (exprD' tus tvs t e1) eqn :?; try congruence.
inversion Heqo; subst; clear Heqo. split. eexists. apply Heqo2.
simpl in H. 
destruct (exprD' tus tvs ty1 e2) eqn:?; try congruence.
eexists; eauto.
Qed.

Ltac destruct_match H :=
match type of H with
| context [ match ?x with _ => _  end] => destruct x eqn:?
end.


Lemma typeof_app : forall e1 e2 t tvs tus,
typeof_expr tus tvs (App e1 e2) = Some t ->
exists t2, typeof_expr tus tvs e1 = Some (tyArr t2 t) /\
typeof_expr tus tvs e2 = Some (t2). 
Proof.
intros. change (App e1 e2) with (AppN.apps e1 (e2 :: nil)) in *.
rewrite AppN.typeof_expr_apps in H; auto with typeclass_instances.
unfold AppN.typeof_apps in H. 
destruct (typeof_expr tus tvs e1) eqn:?; try congruence.
destruct t0; try (simpl in H; destruct_match H;  congruence).
simpl in H.
repeat (destruct_match H; try congruence).
destruct_match Heqo1; try congruence. subst. inversion H.
subst. 
eexists. split. reflexivity. auto.
Qed.

Lemma exprD_ex_typs : forall tus tvs t e1 e2 v,
exprD' tus tvs t (App e1 e2) = Some v ->
exists t2, typeof_expr tus tvs e1 = Some (tyArr t2 t) /\
typeof_expr tus tvs e2 = Some (t2). 
intros.
assert (X := @exprD'_typeof_expr typ _ _ _ _ _ _ _ tus (App e1 e2) tvs
t v). 
assert (H2 : typeof_expr tus tvs (App e1 e2) = Some t).
apply X. intuition. clear X.
apply typeof_app; eauto.
Qed.

intros.
destruct (exprD_ex_L_typ _ _ _ _ _ _ H).
destruct (exprD_ex_R_typ _ _ _ _ _ _ H).
eexists; split; eauto.


exists 
Proof.
intros.
assert (X := @exprD'_typeof_expr typ _ _ _ _ _ _ _ tus (App e1 e2) tvs
ty2 v). 
assert (H2 : typeof_expr tus tvs (App e1 e2) = Some ty2).
apply X. intuition. clear X.
apply typeof_app in H2. destruct H2. destruct H0. eexists; eauto.
Qed.


Lemma set_reif_eq2 :
forall tus tvs typ i vr tr,
exprD' tus tvs (typtree typ) (App (App (Inj (inr (Data (fset typ i)))) vr) tr)  =
exprD' tus tvs (typtree typ) (set_reif i vr tr typ).
Proof.
intros. 
induction i;
simpl;
destruct (as_tree tr) eqn:?; destruct_as_tree; auto.
apply as_tree_l in Heqo. subst.
unfold node in *.
unfold func in *.  
destruct (exprD' tus tvs (typtree typ)
     (App (App (Inj (inr (Data (fset typ i~1)))) vr)
        (App (App (App (Inj (inr (Data (fnode t)))) e1) e0) e))) eqn:Eql,
(exprD' tus tvs (typtree typ)
     (App (App (App (Inj (inr (Data (fnode t)))) e1) e0)
        (set_reif i vr e typ))) eqn :Eqr; auto.
destruct (exprD_ex_L_typ _ _ _ _ _ _ Eql).

destruct (exprD'_ex_L_typ in Eql.

 unfold exprD' at 2.  simpl.
rewrite exprD'_App_L_rw at 1.
erewrite exprD'_App_L_rw.
erewrite exprD'_App_L_rw.
 Focus 2. simpl.

destruct (exprD_ex_R_typ _ _ _ _ _ _ Heqo).
eapply exprD'_App_R_typ in Heqo; eauto.
destruct Heqo. destruct H. destruct H0.
eapply exprD'_App_R_typ in H.
destruct H. destruct H. destruct H1. 

simpl. destruct t; simpl in H2; try congruence.
destruct (typ_eq_dec t0 t1) eqn : ?; try congruence. 
inversion H2; subst; clear H2. 
inversion H0; subst; clear H0.
simpl in H.
change (App e1 e2) with (AppN.apps e1 (e2 :: nil)) in *.
clear Heqs. 
rewrite AppN.exprD'_apps in H; auto with typeclass_instances.
unfold AppN.apps_sem' in H. 
destruct (typeof_expr tus tvs e1) eqn:?; try congruence.
destruct (exprD' tus tvs t e1) eqn :?; try congruence.
inversion Heqo; subst; clear Heqo. split. eexists. apply Heqo2.
simpl in H. 
destruct (exprD' tus tvs ty1 e2) eqn:?; try congruence.
eexists; eauto.


Focus 2. simpl. 


erewrite exprD'_App_L_rw in Heqo. Focus 3.
erewrite exprD'_App_L_rw; eauto. simpl. unfold typeof_func_opt. reflexivity.


simpl. unfold exprD'. 
(* unfold funcAs. destruct typ eqn:?. Focus 2. simpl. reflexivity.
 simpl.
unfold typeof_sym. unfold func_defs.RSym_sym.

Focus 2. simpl.*)

Admitted.


Existing Instance SymSum.RSymOk_sum.
(*Instance RSym_env : RSym SymEnv.func := SymEnv.RSym_func fs.

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
Admitted. *)

End tbled.