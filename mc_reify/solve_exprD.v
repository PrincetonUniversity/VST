Require Import  Coq.Numbers.BinNums.
Require Import compcert.lib.Maps.
Require Import mc_reify.func_defs.
Require Import mc_reify.get_set_reif.
Require Import ExtLib.Tactics.
Require Import VST.floyd.client_lemmas.

Ltac destruct_match H :=
match type of H with
| context [ match ?x with _ => _  end] => destruct x eqn:?
end.

Section tbled.

Variable tbl : SymEnv.functions RType_typ.

Let RSym_sym := RSym_sym tbl.
Existing Instance RSym_sym.

Let RSym_sym_ok :  RSymOk RSym_sym := _.
Existing Instance RSym_sym_ok.


Let Expr_expr_fs := Expr_expr_fs tbl.
Existing Instance Expr_expr_fs.

Let Expr_ok_fs := Expr_ok_fs tbl.
Existing Instance Expr_ok_fs.

Existing Instance MA.

Lemma exprD'_App_R_typ  (e1 e2 : expr typ func) tus tvs ty1 ty2 v:
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

Lemma exprD'_App_L_typ  (e1 e2 : expr typ func) tus tvs ty1 ty2 v:
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

Lemma exprD_typeof_Some : forall tus tvs t (e : expr typ func) val,
exprD' tus tvs t e = Some val -> typeof_expr tus tvs e = Some t.
Proof.
intros.
eapply ExprTac.exprD_typeof_Some; try apply _. eauto.
Qed.

Lemma typeof_app : forall (e1 e2 : expr typ func) t tvs tus,
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

Lemma exprD_ex_typs : forall tus tvs t (e1 e2 : expr typ func) v,
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

Lemma exprD'_one_type : forall tus tvs t1 t2 (e : expr typ func) v1 v2,
exprD' tus tvs t1 e = Some v1 ->
exprD' tus tvs t2 e = Some v2 ->
t1 = t2.
Proof.
intros.
apply ExprTac.exprD_typeof_Some in H; try apply _.
eapply ExprTac.exprD_typeof_eq in H0. symmetry.
eauto. apply _. apply _. apply _. auto.
Qed.


End tbled.


Ltac inv H := inversion H; first [subst | subst_any]; clear H.

Ltac inv_some :=
repeat
match goal with
| [ H : Some _ = Some _ |- _] => inv H
| [ H : None = None |- _ ] => clear H
end.

Ltac rewrite_in_match :=
repeat
match goal with
| [ H : ?x = _ |- context[match ?x with _ => _ end]] =>
   rewrite H
| [ H : ?x = _, H1 : context[match ?x with _ => _ end] |- _] =>
   rewrite H in H1
end.

Ltac destruct_match_oneres :=
repeat match goal with
[ H : context[match ?x with _ => _ end] |- _] =>
  (destruct x eqn:?; try congruence); [ idtac ]
end.

Ltac progress_match :=
repeat (rewrite_in_match; destruct_match_oneres).

Ltac try_simpl_typeof :=
try
match goal with
| [ |- context [typeof_expr ?tus ?tvs ?e] ] =>
   let simpd := eval hnf in (typeof_expr tus tvs e) in
   match simpd with
     | Some _ => change (typeof_expr tus tvs e) with simpd; cbv beta iota
   end
| [ H : context [typeof_expr ?tus ?tvs ?e] |- _ ] =>
   let simpd := eval hnf in (typeof_expr tus tvs e) in
   match simpd with
     | Some _ => change (typeof_expr tus tvs e) with simpd in H; cbv beta iota in H
   end
end.


Ltac cautious_simpl :=
repeat (
cbv [Monad.bind Monad.ret OptionMonad.Monad_option
(*Rsym eq_sym Rrefl exprT_App typ2_cast typ2 Typ2_tyArr*)] in *;
try_simpl_typeof).


Ltac p_exprD H1 :=
autorewrite with exprD_rw in H1; try apply _;
cautious_simpl; repeat (progress_match; inv_some).

Ltac cleanup_dups :=
  repeat
    match goal with
      | [ H : ?x = Some _, H2 : ?x = Some _ |- _ ] => rewrite H in H2; inv_some
      | [ H : ?x = ?x |- _] => clear H
    end.

Ltac remove_no_cast :=
repeat
match goal with
[ H : type_cast ?x ?x = Some _ |- _] => clear H
end.

Ltac subst_rty :=
repeat
match goal with
| [ H : Rty _ _ |- _ ] => unfold Rty in H; inversion H; subst; remove_no_cast;
                          try clear H
end.

Ltac inv_same_types tbl :=
repeat
match goal with
 [ H : exprD' ?tus ?tvs ?t1 ?e = Some ?v1,
   H1 : exprD' ?tus ?tvs ?t2 ?e = Some ?v2 |- _] =>
let N := fresh "H" in assert (N := exprD'_one_type tbl tus tvs t1 t2 e v1 v2 H H1); subst; try inv N; cleanup_dups
end.

Ltac p_exprD_app tbl :=
  repeat
    (match goal with
       | [ H : exprD' _ _ _ (App _ _ ) = (*Some*) _ |- _ ] => p_exprD H
       | [ H : context [match exprD' _ _ _ (App _ _) with _ => _ end] |- _] =>
         p_exprD H
    end;
  cleanup_dups; subst_rty; inv_same_types tbl).

Ltac solve_funcAs :=
repeat
match goal with
| [ H : context [funcAs _ _] |- _ ]  =>
  unfold funcAs in H; simpl in H;
repeat (rewrite type_cast_refl in H; try apply _; unfold Rcast, Relim in H; simpl in H)
| [ |- context [funcAs _ _ ] ]=> unfold funcAs; simpl;
repeat (try rewrite type_cast_refl; try apply _; unfold Rcast, Relim; simpl)
end;
repeat (try rewrite type_cast_refl; try apply _; unfold Rcast, Relim; simpl).

Ltac solve_funcAs_f H :=
  p_exprD H;
  solve_funcAs H;
  match type of H with
    | match ?f with _ => _ end = _ =>
      let eqn := fresh "eqn" in
      let v := fresh "v" in
      (destruct f as [v | ]; try congruence);
        clear H; unfold Rty in v; inversion v; subst; try clear v
  end.





Ltac p_exprD_inj tbl :=
repeat (
match goal with
| [ H : exprD' ?tus ?tvs ?t (Inj ?e ) = Some ?val |- _ ] =>
let X := fresh "X" in
     (assert (X := exprD_typeof_Some tbl tus tvs t (Inj e) val);
     simpl in X; specialize (X H); inv X);
       p_exprD H; ( solve_funcAs || fail)
| [ H : context [match exprD' ?tus ?tvs ?t (Inj ?e ) with _ => _ end] |- _ ] =>
       p_exprD H; ( solve_funcAs || fail)
| [ H : exprD' ?tus ?tvs ?t (Inj ?e ) = _ |- _ ] =>
       p_exprD H; ( solve_funcAs || fail)
end; unfold Rcast in *; cautious_simpl; inv_some; subst_rty);
cleanup_dups; try apply _; inv_some.



Ltac copy H :=
  match type of H with
    | ?x => assert x by exact H
  end.

Ltac pose_exprD' :=
  repeat
    match goal with
      | [ H : typeof_expr ?tus ?tvs ?v = Some ?t  |- _ ] =>
        match goal with
          | [H' : exprD' tus tvs t v = Some _ |- _ ] => fail 1
          | _ => match type of H with
                   | ?x => let X := fresh "H" in
                       assert x as X by exact H;
                       rewrite (ExprFacts.exprD'_typeof_expr tus tvs v t) in X;
                       destruct X
                 end
        end
    end.

Ltac pose_types tbl :=
             repeat
             match goal with
               | [ H : exprD' ?tus ?tvs ?ty ?v = Some ?r  |- _ ] =>
                   match goal with
                     | [H' : typeof_expr tus tvs v = Some ty |- _ ] => fail 1
                     | _ => let X := fresh "H" in
                             assert (X := exprD_typeof_Some tbl tus tvs ty v r H)
                   end
             end.


Ltac solve_exprD tbl :=
repeat (
    p_exprD_app tbl;
    p_exprD_inj tbl;
    autorewrite with exprD_rw; cautious_simpl; solve_funcAs;
    try solve [auto with typeclass_instances | reflexivity | apply _];
    try congruence; pose_types tbl; (*pose_exprD';*) fold func in *;
                                                 progress_match;
    try (rewrite type_cast_refl in *; apply _;
         unfold Rcast, Relim; cautious_simpl);
    try solve [unfold exprT_App in *; simpl; eauto];
    try apply _).



