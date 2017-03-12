Require Import  Coq.Numbers.BinNums.
Require Import compcert.lib.Maps.
Require Import mc_reify.func_defs.

Definition as_list (e : expr typ func) : option
  ((typ * expr typ func * expr typ func) + typ) :=
match e with
  | Inj (inr (Data (fnil ty))) => Some (inr ty)
  | App (App (Inj (inr (Data (fcons ty)))) hd) tl => Some (inl (ty, hd, tl))
  | _ => None
end.

Fixpoint rnth_error (t: typ) (xs: expr typ func) (n: nat) : expr typ func :=
  match as_list xs with
  | Some (inr ty) => none_reif ty
  | Some (inl (ty, hd, tl)) =>
    match n with
    | O => some_reif hd ty
    | S n0 => rnth_error ty tl n0
    end
  | _ => App (Inj (inr (Data (fnth_error t n)))) xs
  end.

Fixpoint rreplace_nth (t: typ) (n: nat) (xs: expr typ func) (x: expr typ func) : expr typ func :=
  match as_list xs with
  | Some (inr ty) => xs
  | Some (inl (ty, hd, tl)) =>
    match n with
    | O => App (App (Inj (inr (Data (fcons ty)))) x) tl
    | S n0 => App (App (Inj (inr (Data (fcons ty)))) hd) (rreplace_nth t n0 tl x)
    end
  | _ => App (App (Inj (inr (Data (freplace_nth t n)))) xs) x
  end.

Require Import ExtLib.Tactics.
Require Import solve_exprD.

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

Definition reflect tus tvs e (ty : typ)
 := @exprD _ _ _ Expr_expr_fs tus tvs e ty.

Lemma some_none: forall T v, @None T = Some v -> False.
intros. congruence.
Qed.

Lemma as_list_cons : forall e t hd tl,
  as_list e = Some (inl (t, hd, tl)) ->
  e = App (App (Inj (inr (Data (fcons t)))) hd) tl.
Proof.
  intros.
  unfold as_list in H.
  repeat
  match goal with
  | [ H : match ?x with _ => _  end = _ |- _ ] => destruct x;
    try (apply some_none in H; contradiction) end.
  congruence.
  inversion H. subst. auto.
Qed.

Lemma as_list_nil : forall e t,
  as_list e = Some (inr t) ->
  e = Inj (inr (Data (fnil t))).
Proof.
  intros.
  unfold as_list in H.
  repeat
  match goal with
  | [ H : match ?x with _ => _  end = _ |- _ ] => destruct x;
    try (apply some_none in H; contradiction) end.
  inversion H. subst. auto.
  congruence.
Qed.

Ltac solve_exprD := solve_exprD.solve_exprD tbl.

Opaque type_cast.

Ltac destruct_as_list :=
repeat
match goal with
| [ H : context [ match as_list ?x with _ => _ end] |- _] => destruct (as_list x) eqn:?
| [ |- context [ match as_list ?x with _ => _ end]] => destruct (as_list x) eqn:?
| [ H : as_list _ = Some (inr _) |- _ ] => apply as_list_nil in H
| [ H : as_list _ = Some (inl (_ , _, _)) |- _ ] => apply as_list_cons in H
| [ H : as_list _ = Some (inl (?p, _)) |- _ ] => destruct p
| [ H : as_list _ = Some (inl ?p) |- _ ] => destruct p
| [ H : as_list _ = Some ?p |- _ ] => destruct p
end;
subst.

Lemma rnth_error_eq2 :
forall typ xs n tus tvs val,
exprD' tus tvs (tylist typ) xs = Some val ->
exprD' tus tvs (tyoption typ) (App (Inj (inr (Data (fnth_error typ n)))) xs)  =
exprD' tus tvs (tyoption typ) (rnth_error typ xs n).
Proof.
intros.
match goal with
        [ |- ?l = ?r ] => destruct l eqn:?, r eqn:?
    end; auto.
  + solve_exprD. simpl in *. unfold exprT_App. simpl. rewrite <- Heqo0.
    clear Heqo0 e0.
    generalize dependent e2.
    generalize dependent xs.
    induction n; intros.
      - simpl in *. unfold some_reif, none_reif in *.
        destruct_as_list; solve_exprD.
      - simpl in *. unfold some_reif, none_reif in *.
        destruct_as_list; solve_exprD.
  + solve_exprD.
    unfold exprT_App; simpl.
    generalize dependent e1.
    generalize dependent xs.
    induction n; intros.
      - simpl in *. unfold some_reif, none_reif in *.
        destruct_as_list; solve_exprD.
      - simpl in *. unfold some_reif, none_reif in *.
        destruct_as_list; solve_exprD.
  + unfold RSym_sym in *. solve_exprD.
Qed.

Lemma typeof_rreplace_nth: forall t xs x n tus tvs,
  typeof_expr tus tvs xs = Some (tylist t) ->
  typeof_expr tus tvs x = Some t ->
  typeof_expr tus tvs (rreplace_nth t n xs x) = Some (tylist t).
Proof.
  intros.
  revert xs H.
  induction n; intros.
  + simpl.
    destruct_as_list.
    - simpl in H |- *.
      progress_match; simpl.
      unfold Rty in *; subst; simpl.
      inv_some.
      solve_exprD.
    - auto.
    - solve_exprD.
  + simpl. destruct_as_list.
    - simpl in H |- *.
      progress_match; simpl.
      unfold Rty in *; subst; simpl.
      inv_some.
      rewrite IHn by auto.
      solve_exprD.
    - auto.
    - solve_exprD.
Qed.

Lemma rreplace_nth_eq2 :
forall typ xs x n tus tvs val v,
exprD' tus tvs (tylist typ) xs = Some val ->
exprD' tus tvs typ x = Some v ->
exprD' tus tvs (tylist typ) (App (App (Inj (inr (Data (freplace_nth typ n)))) xs) x)  =
exprD' tus tvs (tylist typ) (rreplace_nth typ n xs x).
Proof.
  fold func in *; unfold RSym_sym in *.
  intros.
  match goal with
        [ |- ?l = ?r ] => destruct l eqn:?, r eqn:?
    end; auto.
  + solve_exprD. simpl in *. unfold exprT_App. simpl. rewrite <- Heqo0.
    clear Heqo0 e0.
    generalize dependent e2.
    generalize dependent xs.
    induction n; intros.
      - simpl in *. unfold some_reif, none_reif in *.
        destruct_as_list; solve_exprD.
      - simpl in *. unfold some_reif, none_reif in *.
        destruct_as_list; solve_exprD.
        simpl in H0.
        progress_match.
        solve_exprD.
        unfold Rty in r; subst.
        solve_exprD.
        unfold exprT_App; simpl.
        erewrite <- IHn with (e2 := e3); eauto.
  + solve_exprD.
    unfold exprT_App; simpl.
    generalize dependent e1.
    generalize dependent xs.
    induction n; intros.
      - simpl in *. unfold some_reif, none_reif in *.
        destruct_as_list; solve_exprD.
      - simpl in *. unfold some_reif, none_reif in *.
        destruct_as_list; solve_exprD.
        rewrite typeof_rreplace_nth in Heqo0 by auto.
        solve_exprD.
        specialize (IHn e Heqo4 Heqo2 _ Heqo5).
        inversion IHn.
  + unfold RSym_sym in *. solve_exprD.
Qed.

End tbled.