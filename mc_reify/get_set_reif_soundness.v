Require Import  Coq.Numbers.BinNums.
Require Import compcert.lib.Maps.
Require Import mc_reify.func_defs.
Require Import mc_reify.get_set_reif.
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


Lemma as_tree_l : forall e t l o r,
as_tree e = Some (inl (t, l, o, r)) ->
e = (App (App (App (Inj (inr (Data (fnode t)))) l) o) r).
intros.
unfold as_tree in H.
repeat
match goal with
| [ H : match ?x with _ => _  end = _ |- _ ] => destruct x;
  try (apply some_none in H; contradiction) end.
congruence.
inversion H. subst. auto.
Admitted. (*Qed.*)


Lemma as_tree_r : forall e t,
as_tree e = Some (inr t) ->
e = (Inj (inr (Data (fleaf t)))).
intros.
unfold as_tree in H.
repeat
match goal with
| [ H : match ?x with _ => _  end = _ |- _ ] => destruct x; simpl in H;  try congruence end.
inversion H. subst. auto.
Admitted.

Ltac destruct_as_tree :=
repeat
match goal with
| [ H : context [ match as_tree ?x with _ => _ end] |- _] => destruct (as_tree x) eqn:?
| [ H : as_tree _ = Some (inl (_ , _ , _, _)) |- _ ] => apply as_tree_l in H
| [ H : as_tree _ = Some (inr _) |- _ ] => apply as_tree_r in H
| [ H : as_tree _ = Some (inl (?p, _, _)) |- _ ] => destruct p
| [ H : as_tree _ = Some (inl (?p, _)) |- _ ] => destruct p
| [ H : as_tree _ = Some (inl ?p) |- _ ] => destruct p
| [ H : as_tree _ = Some ?p |- _ ] => destruct p
end;
subst.

Ltac solve_exprD := solve_exprD.solve_exprD tbl.

Opaque type_cast.

Lemma get_reif_val_exists :
forall i tr typ tus tvs vtr,
exprD' tus tvs (typtree typ) tr = Some vtr ->
exists v, exprD' tus tvs (tyoption typ) (get_reif i tr typ) = Some v.
unfold RSym_sym.
induction i; intros; simpl in *;
destruct (as_tree tr) eqn:?; destruct_as_tree; solve_exprD; unfold none_reif; solve_exprD.
Qed.

Lemma get_reif_eq2 :
forall typ i tr tus tvs val,
exprD' tus tvs (typtree typ) tr = Some val ->
exprD' tus tvs (tyoption typ) (App (Inj (inr (Data (fget typ i)))) tr)  =
exprD' tus tvs (tyoption typ) (get_reif i tr typ) .
Proof.
intros.
match goal with
        [ |- ?l = ?r ] => destruct l eqn:?, r eqn:?
    end; auto.
  + solve_exprD. simpl in *. unfold exprT_App. simpl. rewrite <- Heqo0.
    clear Heqo0 e0.
    generalize dependent e2.
    generalize dependent tr.
    induction i; intros.
      - simpl in *. destruct_as_tree.
          * solve_exprD.
          * unfold none_reif. solve_exprD.
          * simpl in *. solve_exprD.
      - simpl in *; destruct_as_tree.
          * solve_exprD.
          * unfold none_reif. solve_exprD.
          * simpl in *. solve_exprD.
      - simpl in *. destruct_as_tree.
          * solve_exprD.
          * unfold none_reif. solve_exprD.
          * solve_exprD.
  + solve_exprD.
    edestruct (get_reif_val_exists); eauto.
    rewrite H0 in Heqo0. congruence.
  + unfold RSym_sym in *. solve_exprD.
Admitted.

Lemma set_reif_istree :
  forall i tus tvs t0 vr e t x,
    exprD' tus tvs t0 (set_reif i vr e t) = Some x ->
    t0 = typtree t.
Proof.

simpl in *.
induction i; intros; simpl in *; unfold leaf, node, some_reif, none_reif in *.
  + destruct_as_tree;
      solve_exprD.
  + destruct_as_tree; solve_exprD; specialize (IHi tus tvs (typtree t1));
      try eapply IHi in H5; try eapply IHi in H3; auto.
  + destruct_as_tree; subst;
      solve_exprD.
(*Time Qed.*)
Admitted.


Lemma set_reif_exprD :
forall tus tvs typ i vr e v ev,
exprD' tus tvs (typtree typ) e = Some ev ->
exprD' tus tvs typ vr = Some v ->
exists r, exprD' tus tvs (typtree typ) (set_reif i vr e typ) = Some r.
Proof.
induction i; intros; simpl in *; unfold leaf, node, some_reif, none_reif in *;
destruct (as_tree e) eqn:?; destruct_as_tree;
      unfold RSym_sym in *; solve_exprD; eauto.
  + edestruct (IHi vr e0); eauto; solve_exprD; eauto.
  + edestruct (IHi vr (Inj (inr (Data (fleaf typ))))); eauto; solve_exprD.
  + edestruct (IHi vr e2); eauto; solve_exprD.
  + edestruct (IHi vr (Inj (inr (Data (fleaf typ))))); eauto; solve_exprD.
Admitted.
 (*Qed.*)

Lemma set_reif_vr : forall tus tvs typ i e vr e4,
  exprD' tus tvs (typtree typ) (set_reif i vr e typ) = Some e4 ->
  exists v, exprD' tus tvs typ vr = Some v.
Proof.
induction i; intros; simpl in *; unfold leaf, node, some_reif, none_reif in *;
    destruct_as_tree;
      solve_exprD; eauto.
Admitted. (*Qed.*)

Ltac extract_set_reif_type :=
repeat
match goal with
| [ H : exprD' ?tus ?tvs (typtree ?t) (set_reif _ _ _ _) = _ |- _] => fail 1
| [ H : exprD' ?tus ?tvs ?t (set_reif ?i ?vr ?e ?t0) = Some ?x |- _] =>
pose proof (set_reif_istree i tus tvs t vr e t0 x H); subst; try congruence
end.


Ltac set_reif_ex :=
match goal with
|  [ H : exprD' ?tus ?tvs (typtree ?t) (set_reif ?i ?vr ?e ?t) = None |- _ ] =>
      edestruct (set_reif_exprD tus tvs t i vr e); eauto; fold func in *;
try congruence
| [ H : context[match typeof_expr ?tus ?tvs (set_reif ?i ?vr ?e ?t) with _ => _ end ] |- _ ] =>
  edestruct (set_reif_exprD tus tvs t i vr e); eauto; pose_types; fold func in *;  forward
end.

Lemma typeof_set_reif_None_F :
forall tus tvs i e t ev vr v,
exprD' tus tvs (typtree t) e = Some ev ->
exprD' tus tvs t vr = Some v ->
typeof_expr tus tvs (set_reif i vr e t) = None ->
False.
intros.
edestruct (set_reif_exprD); eauto.
instantiate (1 := i) in H2.
solve_exprD. unfold RSym_sym in *.
fold func in *. congruence.
Qed.

Ltac set_typeof_None :=
  match goal with
    | [H: typeof_expr ?tus ?tvs (set_reif ?i ?vr ?e ?t) = None |- _ ] =>
      try solve [eapply typeof_set_reif_None_F in H; first [progress eauto | solve_exprD]; try contradiction]
end.

Ltac get_vr_type :=
repeat
match goal with
|  [ H :  exprD' ?tus ?tvs (typtree ?typ) (set_reif ?i ?vr ?e ?typ) = Some ?v |- _ ] =>
   match goal with
     | [ H': exprD' tus tvs typ vr = Some _ |- _] => fail 1
     | _ => destruct (set_reif_vr _ _ typ _ _ _ _ H)
   end
end.

Ltac set_reif_tac :=
repeat (unfold RSym_sym in *;
        solve_exprD;
        try set_reif_ex;
        extract_set_reif_type;
        try set_typeof_None;
        try (progress get_vr_type; pose_types tbl)
        ).



Lemma set_reif_eq2 :
forall i tus tvs typ vr tr val,
exprD' tus tvs (typtree typ) tr = Some val ->
exprD' tus tvs (typtree typ) (App (App (Inj (inr (Data (fset typ i)))) vr) tr)  =
exprD' tus tvs (typtree typ) (set_reif i vr tr typ).
Proof.
intros.
unfold RSym_sym in *.
match goal with
        [ |- ?l = ?r ] => destruct l eqn:?, r eqn:?
    end; auto.
  - solve_exprD. unfold exprT_App. simpl. fold func in *.
    simpl in Heqo0. rewrite <- Heqo0.
    clear Heqo0 e0.
    generalize dependent vr. generalize dependent tr. revert e2 e3.
    induction i; intros; simpl in *;
    unfold node, leaf, some_reif, none_reif in *;

    destruct_as_tree; solve_exprD.
    + pose_exprD'.
      solve_exprD. unfold exprT_App. simpl.
      erewrite <- IHi in *; auto. inversion Heqo10. auto.  auto. auto.
    + pose_exprD'. solve_exprD. unfold exprT_App. simpl.
      erewrite <- IHi in *; eauto. inversion Heqo2.
      Focus 2. solve_exprD. simpl. auto.
    + pose_exprD'. solve_exprD. erewrite <- IHi in *; eauto. inv Heqo11. auto.
    + pose_exprD'. solve_exprD. unfold exprT_App. simpl. erewrite <- IHi in *; eauto.
      inversion Heqo6. Focus 2. solve_exprD. auto.
  - set_reif_tac.
  - set_reif_tac.
Admitted.

End tbled.