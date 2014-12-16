Require Import  Coq.Numbers.BinNums.
Require Import compcert.lib.Maps.
Require Import mc_reify.func_defs.
Require Import mc_reify.get_set_reif.
Require Import mc_reify.app_lemmas.
Require Import ExtLib.Tactics.


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

Section TypeOfFunc.
  Context {typ func : Type}.
  Context {RType_typ : RType typ}.
  Context {RTypeOk_typ : RTypeOk}.
  Context {RSym_func : RSym func}.

    Lemma typeof_funcAs f t e (H : funcAs f t = Some e) : typeof_sym f = Some t.
    Proof.
      unfold funcAs in H.
      generalize dependent (symD f).
      destruct (typeof_sym f); intros; [|congruence].
      destruct (type_cast t0 t); [|congruence].
      destruct r; reflexivity.
    Qed.
   
   Lemma funcAs_Some f t (pf : typeof_sym f = Some t) :
        funcAs f t =
        Some (match pf in (_ = z)
          return match z with
                   | Some z' => TypesI.typD z'
                   | None => unit
                 end
          with
          | eq_refl => symD f
          end).
      Proof.
        unfold funcAs.
        generalize (symD f).
        rewrite pf. intros.
        rewrite type_cast_refl. reflexivity. apply _.
      Qed.

End TypeOfFunc.

Lemma set_denote : forall i ty tus tvs,
exprD' tus tvs (tyArr ty (tyArr (typtree ty) (typtree ty)))
     (Inj (inr (Data (fset ty i)))) = 
(Some ( fun _ _ => @PTree.set (typD ty ) i)).
Proof.
intros.
autorewrite with exprD_rw. simpl.
unfold funcAs.
simpl (typeof_sym (inr (Data (fset ty i)))).
unfold typeof_func_opt. rewrite type_cast_refl. simpl. reflexivity.
apply _.
Qed.

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

Ltac inv H := inversion H; subst; clear H.

Ltac inv_some :=
repeat 
match goal with
| [ H : Some _ = Some _ |- _] => inv H
| [ H : None = None |- _ ] => clear H
end. 


Ltac p_exprD H1 :=
autorewrite with exprD_rw in H1;
simpl in H1; repeat (forward; inv_some).

Ltac cleanup_dups :=             
  repeat
    match goal with 
      | [ H: exprD' _ _ _ ?x = Some _, 
             H1 : exprD' _ _ _ ?x = Some _ |- _] => try rewrite H in *; inv_some
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

Lemma exprD'_one_type : forall tus tvs t1 t2 e v1 v2,
exprD' tus tvs t1 e = Some v1 ->
exprD' tus tvs t2 e = Some v2 ->
t1 = t2.
Proof.
intros.
apply ExprTac.exprD_typeof_Some in H; try apply _.
eapply ExprTac.exprD_typeof_eq in H0. symmetry.
eauto. apply _. apply _. apply _. auto.
Qed.


Ltac inv_same_types :=
repeat
match goal with
 [ H : exprD' ?tus ?tvs ?t1 ?e = Some ?v1,
   H1 : exprD' ?tus ?tvs ?t2 ?e = Some ?v2 |- _] => 
let N := fresh "H" in assert (N := exprD'_one_type tus tvs t1 t2 e v1 v2 H H1); subst; try inv N
end.

Ltac p_exprD_app :=
  repeat
    (match goal with
        [ H : exprD' _ _ _ (App _ _ ) = (*Some*) _ |- _ ] => p_exprD H
    end; 
  cleanup_dups; subst_rty; inv_same_types).

Ltac solve_funcAs :=
repeat
match goal with 
| [ H : funcAs _ _ = (*Some*) _ |- _ ]  =>  unfold funcAs in H; simpl in H;  rewrite type_cast_refl in H
end.

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

Lemma exprD_typeof_Some : forall tus tvs t e val,
exprD' tus tvs t e = Some val -> typeof_expr tus tvs e = Some t.
Proof.
intros.
eapply ExprTac.exprD_typeof_Some; try apply _. eauto.
Qed. 


Ltac p_exprD_inj :=
repeat (
match goal with
[ H : exprD' ?tus ?tvs ?t (Inj ?e ) = Some ?val |- _ ] =>
let X := fresh "X" in
     (assert (X := exprD_typeof_Some tus tvs t (Inj e) val);
     simpl in X; specialize (X H); inv X); 
       p_exprD H; ( solve_funcAs || fail)
end; unfold Rcast in *; simpl in *; inv_some; subst_rty);
cleanup_dups; try apply _; inv_some.


Ltac copy H :=
                  match type of H with 
                      | ?x => assert x by exact H
                  end.



Opaque type_cast.

Lemma set_reif_istree :
  forall i tus tvs t0 vr e t x,
    exprD' tus tvs t0 (set_reif i vr e t) = Some x ->
    t0 = typtree t.
Proof.
simpl in *.
induction i; intros.
  + simpl in *.
    destruct (as_tree e) eqn:?;
      destruct_as_tree.
      - clear Heqo.
        unfold node in *.
        specialize (IHi tus tvs t0 vr e0 t).
        p_exprD_app; p_exprD_inj. eauto.
      - clear Heqo.       
        specialize (IHi tus tvs t0 vr (leaf t1) t). 
        simpl in *. unfold none_reif, node in *.
        p_exprD_app; p_exprD_inj. eauto.
      - p_exprD_app; p_exprD_inj; eauto.
  + simpl in *.
    destruct (as_tree e) eqn:?; destruct_as_tree.
      - clear Heqo.
        unfold node in *.
        specialize (IHi tus tvs t0 vr e2 t).
        p_exprD_app; p_exprD_inj. eauto.
      - clear Heqo.       
        specialize (IHi tus tvs t0 vr (leaf t1) t). 
        simpl in *. unfold none_reif, node in *.
        p_exprD_app; p_exprD_inj. eauto.
      - p_exprD_app; p_exprD_inj. 
  + simpl in *.
    destruct (as_tree e) eqn:?; destruct_as_tree.
      - unfold node in *. unfold some_reif in *.
        p_exprD_app; p_exprD_inj; eauto.
      - clear Heqo.
        unfold node in *. p_exprD_app; p_exprD_inj. 
      - clear Heqo.       
        simpl in *. unfold none_reif, node in *.
        p_exprD_app; p_exprD_inj. 
Qed.        

Lemma set_reif_exprD :
forall tus tvs typ i vr v ev e,
exprD' tus tvs (typtree typ) e = Some ev ->
exprD' tus tvs typ vr = Some v ->
exists r, exprD' tus tvs (typtree typ) (set_reif i vr e typ) = Some r.
Proof.
induction i; intros.
  + simpl in *.
    destruct (as_tree e) eqn:?; destruct_as_tree.
      - apply as_tree_l in Heqo. subst. unfold node in *.
        match goal with 
            [ |- exists r, ?l = _] => destruct l eqn:?
        end.
          * p_exprD_app; p_exprD_inj. eauto.
          * p_exprD_app; p_exprD_inj.
            {  repeat match type of Heqo with
                    | match ?x with _ => _ end = _ => destruct x eqn:?
                end.
               - simpl in *. unfold exprT_App in *. simpl in *. congruence.
               - p_exprD_app; p_exprD_inj.
                 edestruct IHi.
                 apply H2.
                 apply H0.
                 fold func in *.
                 congruence.
               - p_exprD_app.
                 p_exprD H7.
                 rewrite ExprFacts.exprD'_typeof_expr in Heqo0.
                 destruct Heqo0.
                 apply set_reif_istree in H7. subst.
                 solve_funcAs. inversion H6. 
                 apply _.
               - edestruct IHi.
                 apply H2.
                 eauto.
                 fold func in *. 
                 assert (X := ExprFacts.exprD'_typeof_expr tus tvs (set_reif i vr e0 typ) (typtree typ)).
                 destruct X. rewrite H8 in Heqo0. congruence.
                 eauto. }
      - apply as_tree_r in Heqo.
        subst. unfold node, leaf, none_reif in *.
        p_exprD_inj.
        match goal with 
            [ |- exists r, ?l = _] => destruct l eqn:?
        end; eauto.
          * p_exprD_app; p_exprD_inj. 
            {  repeat match type of Heqo with
                    | match ?x with _ => _ end = _ => destruct x eqn:?
                end.
               - simpl in *. unfold exprT_App in *. simpl in *. congruence.
               - p_exprD_app; p_exprD_inj.
                rewrite ExprFacts.exprD'_typeof_expr in Heqo0.
                 destruct Heqo0.
                 simpl in *.
                 edestruct (IHi vr v).
                 instantiate (2 := (Inj (inr (Data (fleaf typ))))).
                 autorewrite with exprD_rw. simpl. forward. auto.
                 congruence.
               - p_exprD_app.
                 repeat match type of Heqo1 with
                    | match ?x with _ => _ end = _ => destruct x eqn:?
                end; forward; try congruence.
                   + p_exprD Heqo2. solve_funcAs; try apply _.
                     inversion H.
                   + p_exprD_app; p_exprD_inj.
                     repeat match type of Heqo with
                    | match ?x with _ => _ end = _ => destruct x eqn:?
                end; forward; try congruence.
                     p_exprD_app; p_exprD_inj.
                     p_exprD Heqo2. solve_funcAs; try apply _; inversion H.
                     rewrite ExprFacts.exprD'_typeof_expr in Heqo0.
                     destruct Heqo0.
                     p_exprD_inj.
                     edestruct (IHi vr v).
                     instantiate (2 := (Inj (inr (Data (fleaf typ))))).
                     autorewrite with exprD_rw. simpl. unfold funcAs.
                     simpl. rewrite type_cast_refl. unfold Rcast.
                     simpl. auto. apply _. auto.
                     apply set_reif_istree in H. subst.
                     p_exprD Heqo1. solve_funcAs.
                     inversion H. apply _.
               - edestruct IHi.
                 instantiate (2 := (Inj (inr (Data (fleaf typ))))).
                 autorewrite with exprD_rw. simpl. unfold funcAs.
                     simpl. rewrite type_cast_refl. unfold Rcast.
                     simpl. auto. apply _. eauto.
                     destruct (ExprFacts.exprD'_typeof_expr tus tvs 
                                ((set_reif i vr (Inj (inr (Data (fleaf typ)))) typ)) (typtree typ)).
                     fold func in *.
                     rewrite H2 in Heqo0.
                     congruence.
                     eexists.  eauto. }
      - clear Heqo. eexists. autorewrite with exprD_rw. simpl.
        assert ( X := exprD_typeof_Some tus tvs (typtree typ) e ev H).
        rewrite X.
        autorewrite with exprD_rw. simpl.
        copy H0.
        apply exprD_typeof_Some in H0. rewrite H0.
        autorewrite with exprD_rw. simpl. 
        unfold funcAs. simpl.
        rewrite type_cast_refl. unfold Rcast, Relim. simpl.
        fold func in *.
        rewrite H1. rewrite H. reflexivity. apply _.
   + simpl in *.
    destruct (as_tree e) eqn:?; destruct_as_tree.
      - apply as_tree_l in Heqo. subst. unfold node in *.
        match goal with 
            [ |- exists r, ?l = _] => destruct l eqn:?
        end.
          * p_exprD_app; p_exprD_inj. eauto.
          * p_exprD_app; p_exprD_inj.
            {  repeat match type of H5 with
                    | match ?x with _ => _ end = _ => destruct x eqn:?
                end.
               - simpl in *. unfold exprT_App in *. simpl in *. congruence.
               - p_exprD_app; p_exprD_inj.
                 edestruct IHi.
                 apply H7.
                 apply H0.
                 fold func in *.
                 congruence.
               - p_exprD_app.
                 p_exprD Heqo0.
                 rewrite ExprFacts.exprD'_typeof_expr in Heqo.
                 destruct Heqo.
                 apply set_reif_istree in H5. subst.
                 solve_funcAs. inversion H6. 
                 apply _.
               - edestruct IHi.
                 apply H7.
                 eauto.
                 fold func in *. 
                 assert (X := ExprFacts.exprD'_typeof_expr tus tvs (set_reif i vr e2 typ) (typtree typ)).
                 destruct X. rewrite H9 in Heqo. congruence.
                 eauto. }
      - apply as_tree_r in Heqo.
        subst. unfold node, leaf, none_reif in *.
        p_exprD_inj.
        match goal with 
            [ |- exists r, ?l = _] => destruct l eqn:?
        end; eauto.
          * p_exprD_app; p_exprD_inj. 
            {  repeat match type of Heqo with
                    | match ?x with _ => _ end = _ => destruct x eqn:?
                end.
               - simpl in *. unfold exprT_App in *. simpl in *. congruence.
               - clear - Heqo1. p_exprD Heqo1. 
                 solve_funcAs. inversion H. apply _. apply _.
               - p_exprD_app.
                 repeat match type of Heqo0 with
                    | match ?x with _ => _ end = _ => destruct x eqn:?
                end; forward; try congruence.
                   + p_exprD Heqo1. solve_funcAs; try apply _.
                     inversion H.
                   + p_exprD_app; p_exprD_inj. 
                     repeat match type of Heqo with
                    | match ?x with _ => _ end = _ => destruct x eqn:?
                end; forward; try congruence.
                     p_exprD_app; p_exprD_inj.
                     rewrite ExprFacts.exprD'_typeof_expr in Heqo0.
                     destruct Heqo0. congruence.
                     rewrite ExprFacts.exprD'_typeof_expr in Heqo0.
                     destruct Heqo0. apply set_reif_istree in H. subst.
                     p_exprD Heqo1.
                     solve_funcAs. inversion H.
                     apply _.
                     edestruct (IHi vr v).
                     instantiate (2 := (Inj (inr (Data (fleaf typ))))).
                     autorewrite with exprD_rw. simpl. unfold funcAs.
                     simpl. rewrite type_cast_refl. unfold Rcast.
                     simpl. auto. apply _. auto. 
                     destruct (ExprFacts.exprD'_typeof_expr tus tvs 
                                ((set_reif i vr (Inj (inr (Data (fleaf typ)))) typ)) (typtree typ)). fold func in *.
                     rewrite H2 in Heqo0. congruence.
                     eauto. }
      - autorewrite with exprD_rw. simpl.
        copy H. fold func in *. 
        assert (X := exprD_typeof_Some _ _ (typtree typ) _ _ H1).
        fold func in *. rewrite X. 
        autorewrite with exprD_rw. simpl. 
        copy H0. apply exprD_typeof_Some in H2. 
        fold func in *. rewrite H2.
        autorewrite with exprD_rw. simpl.
        unfold funcAs. simpl.
        rewrite type_cast_refl. unfold Rcast, Relim. simpl.
        fold func in *.
        rewrite H1. rewrite H0. eauto. apply _.
  + simpl in *.
    destruct (as_tree e) eqn:?; destruct_as_tree.
      - apply as_tree_l in Heqo. subst. p_exprD_app.
        p_exprD_inj. unfold node.
        autorewrite with exprD_rw. simpl.
        forward.
        autorewrite with exprD_rw. simpl.
        forward. copy H0. apply exprD_typeof_Some in H7.
        forward. inv_some. rewrite type_cast_refl.
        unfold some_reif.
        repeat (autorewrite with exprD_rw; simpl; forward; inv_some).
        inv_some. unfold funcAs. simpl. rewrite type_cast_refl.
        simpl. forward. rewrite type_cast_refl. 
        unfold Rcast. simpl. fold func in *. rewrite H0.  eauto.
        auto with typeclass_instances.
        apply _.
        apply _.
      - apply as_tree_r in Heqo. unfold node, leaf, some_reif in *.
        subst. p_exprD_inj.
        copy H0. apply exprD_typeof_Some in H.
        repeat (autorewrite with exprD_rw; simpl; forward; inv_some; 
                try (unfold funcAs; simpl; rewrite type_cast_refl; 
                     unfold Rcast; simpl; forward); fold func in *).
        eauto.
        auto with typeclass_instances.                                         
        apply _.
        apply _.
        apply _.
        apply _.
     -  copy H0. apply exprD_typeof_Some in H1. fold func in *.
        assert (X := exprD_typeof_Some _ _ (typtree typ) _ _ H). 
        repeat (autorewrite with exprD_rw; simpl; forward; inv_some; 
                try (unfold funcAs; simpl; rewrite type_cast_refl; 
                     unfold Rcast; simpl; forward); fold func in *); try apply _.
        eauto. Grab Existential Variables. auto.
Admitted. (*Qed works, is slow *) 

Lemma set_reif_vr : forall tus tvs typ i e vr e4,
  exprD' tus tvs (typtree typ) (set_reif i vr e typ) = Some e4 ->
  exists v, exprD' tus tvs typ vr = Some v.
Proof.
induction i; intros.
  + simpl in *.
    destruct (as_tree e) eqn:?; destruct_as_tree.
      - apply as_tree_l in Heqo.
        subst.
        unfold node in *.
        p_exprD_app.
        p_exprD_inj.
        edestruct IHi.
        eauto.
        eauto.
     - apply as_tree_r in Heqo.
        subst.
        unfold node in *.
        p_exprD_app.
        p_exprD_inj.
        edestruct IHi.
        eauto.
        eauto.
     - p_exprD_app; p_exprD_inj. eauto.
  +  simpl in *.
    destruct (as_tree e) eqn:?; destruct_as_tree.
      - apply as_tree_l in Heqo.
        subst.
        unfold node in *.
        p_exprD_app.
        p_exprD_inj.
        eauto; eauto.
     - apply as_tree_r in Heqo.
        subst.
        unfold node in *.
        p_exprD_app.
        p_exprD_inj.
        eauto; eauto.
     - p_exprD_app; p_exprD_inj.
       eauto.
 + simpl in *.
    destruct (as_tree e) eqn:?; destruct_as_tree.
      - apply as_tree_l in Heqo.
        subst.
        unfold node, some_reif in *.
        p_exprD_app.
        p_exprD_inj.
        eauto. 
     - apply as_tree_r in Heqo.
        subst.
        unfold node, leaf, some_reif in *.
        p_exprD_app.
        p_exprD_inj.  
        eauto. 
     - p_exprD_app; p_exprD_inj.
       eauto.
Admitted (*Qed*).
  

Lemma set_reif_eq2 :
forall i tus tvs typ vr tr val,
exprD' tus tvs (typtree typ) tr = Some val ->
exprD' tus tvs (typtree typ) (App (App (Inj (inr (Data (fset typ i)))) vr) tr)  =
exprD' tus tvs (typtree typ) (set_reif i vr tr typ).
Proof.
induction i;
intros;
simpl. rename H into HX.
  + forward. destruct_as_tree.
     - apply as_tree_l in H. subst.
       unfold node in *.
       unfold func in *.  
destruct (exprD' tus tvs (typtree typ)
     (App (App (Inj (inr (Data (fset typ i~1)))) vr)
        (App (App (App (Inj (inr (Data (fnode t)))) e1) e0) e))) eqn:Eql,
(exprD' tus tvs (typtree typ)
     (App (App (App (Inj (inr (Data (fnode t)))) e1) e0)
          (set_reif i vr e typ))) eqn :Eqr; auto.
            * specialize (IHi tus tvs typ vr e).              
              p_exprD_app.
              unfold exprT_App in *. simpl in *. 
              p_exprD_inj. 
              fold func in *.
              erewrite <- IHi in H1.
              p_exprD_app; p_exprD_inj. inv_some.
              auto.
              eauto.
            * p_exprD_app. p_exprD_inj. 
              fold func in *.
              edestruct (set_reif_exprD tus tvs t0 i vr).
              apply H10. eauto.
              
              copy H5. fold func in *. apply exprD_typeof_Some in H5.
              fold func in *. erewrite H5 in Eqr.
              forward.
              p_exprD_app. p_exprD H13. solve_funcAs.
              inversion H12. apply _.
            * p_exprD_app. p_exprD_inj. 
              rewrite (type_cast_refl (typtree typ)) in Eql.
              rewrite (type_cast_refl (tyoption typ)) in Eql.
              rewrite type_cast_refl in Eql.
              autorewrite with exprD_rw in Eql.
              simpl in Eql. forward.
              destruct (set_reif_vr tus tvs typ _ _ _ _ H1).
              assert (X := exprD_typeof_Some _ _ _ _ _ H7). 
              forward.
              autorewrite with exprD_rw in Eql.
              simpl in Eql. inv_some.
              unfold funcAs in *.
              simpl in *. rewrite type_cast_refl in Eql.
              unfold Rcast, Relim in Eql.
              simpl in Eql. forward. fold func in *. rewrite H7 in Eql.
              autorewrite with exprD_rw in Eql.
              simpl in Eql. forward.
              autorewrite with exprD_rw in H14.
              simpl in H14. forward. inv_some.
              unfold funcAs in H14. simpl in *.
              rewrite type_cast_refl in H14.
              forward. inversion H11. apply _. apply _. apply _.
     - apply as_tree_r in H. subst.              
       p_exprD_inj.
       repeat (autorewrite with exprD_rw; simpl).
       
       
              

              


       
                                                                     
        
         
                
        
        
 

p_exprD_app.
              unfold exprT_App in *. simpl in *.
              p_exprD_inj.
              { match type of Eqr with
                    | match ?x with _ => _ end = _ => destruct x eqn:?
                end. 
                  + destruct (exprD' tus tvs (tyArr t0 (typtree t))
                          (App (App (Inj (inr (Data (fnode t)))) e1) e0)) eqn :?.
                      - destruct (exprD' tus tvs t0 (set_reif i vr e t)) eqn :?.
                          * p_exprD_app.
                            p_exprD_inj. fold func in *. congruence.
                          * forward.
                             specialize (IHi tus tvs t vr e).

                            repeat (p_exprD_app; p_exprD_inj). 
                            p_exprD H12.
                            solve_funcAs.
                            unfold Rcast in H11. simpl in H11. congruence.
                            apply _.
                      - fold func in *.
                        rewrite ExprFacts.exprD'_typeof_expr in Heqo.
                        destruct Heqo. 
                        copy H6.
                        apply set_reif_istree in H6.
                        subst. 
                        specialize (IHi tus tvs t).
                        rewrite <- IHi in H7.
                        p_exprD_app; p_exprD_inj.
                        p_exprD H12.
                        solve_funcAs. inversion H7.
                        apply _.
                + 
                        unfold funcAs in *. simpl in *.
                        
                        simpl in H9. destruct (Rsym r).
                            
                            solve_funcAs_f H11.
                            p_exprD_app; p_exprD_inj.
fold fu
                            assert (
                            
                
                p_exprD Eqr. p_exprD Eqr. 
                destruct ( exprD' tus tvs
                (tyArr (typtree t)
                   (tyArr (tyoption t) (tyArr t0 (typtree t))))
                (Inj (inr (Data (fnode t))))) eqn:?. Focus 2.
                unfold funcAs in Eqr; simpl in Eqr.
                    inv_some.

assert (X := exprD_typeof_Some tus tvs  (tyArr t0 (tyArr (typtree t) (typtree t)))
                        (Inj (inr (Data (fset t i)))) e4). simpl in X.
specialize (X H8). unfold typeof_func_opt in X. inv X.
p_exprD_inj. auto. apply _. apply _.

clear - X H8.  
Set Printing All.

 fold exprT in *.
apply (exprD_typeof_Some _ _ _ _ _ H9).
              pose (@ExprTac.exprD_typeof_Some  _).
              pose (ExprTac.exprD_typeof_Some _ _ _ _ _ ).
              
Check ExprTac.exprD_typeof_Some. in H8.
              p_exprD H11.
              solve_funcAs H7. inv H7.
              
              assert (X := set_denote i~1 typ tus tvs). fold func in *.
              rewrite <- X in *.

              rewrite <- set_denote in H8.
              p_exprD H4.
              unfold funcAs in H4. simpl in H4.
              clear H15 H16.
           Check set_denote.
              rewrite <- IHi in H1.
              p_exprD_app. 
              unfold exprT_App in *. simpl in *.
              p_exprD_inj. 
              unfold Relim, Rsym in H17.
inversion r0. subst.
              rewrite type_cast_refl in H6. inv H6.
              unfold Relim in H13. simpl in H13. rewrite <- H8.
              p_exprD_app.
              p_exprD H9.
              solve_funcAs H7.
              unfold Rcast in H7. simpl in H7. inv_some.
              unfold exprT_App in *.
              simpl in *. 
              copy H8.
              solve_funcAs_f H7.
              p_exprD H8.
              solve_funcAs H7.
              unfold Rcast in H7.
              simpl in H7. inv H7.
              inv H12.
              
              
              solve
              simpl in H8.
              
              p_exprD H6.
              solve_funcAs_f H6. 
              
              solve_funcAs_f H4. 
              solve_funcAs_f H9.
              unfold funcAs in *. simpl in *. 
              unfold Rty in *. subst
              
              rewrite <- IHi in H1. clear IHi.
              p_exprD_app.
              p_exprD H6.
              solve_funcAs_f H6.
              unfold exprT_App; simpl in *. 
              cleanup_dups.
              
end.
              
              rewrite H3 in H12.
              cleanup_dups.
              rewrite <- IHi in H1.
              p_exprD_inj.
              p_exprD_inj.
              unfold exprT_App in *. simpl.
              p_exprD H9.
              solve_funcAs_f H4.
              p_exprD_inj.
              unfold exprT_App. simpl.
              p_exprD H8. *)


Lemma set_reif_eq2 :
forall i tus tvs typ vr tr,
exprD' tus tvs (typtree typ) (App (App (Inj (inr (Data (fset typ i)))) vr) tr)  =
exprD' tus tvs (typtree typ) (set_reif i vr tr typ).
Proof.

induction i;
intros;
simpl.
forward. destruct_as_tree.
apply as_tree_l in H. subst.
unfold node in *.
unfold func in *.  
destruct (exprD' tus tvs (typtree typ)
     (App (App (Inj (inr (Data (fset typ i~1)))) vr)
        (App (App (App (Inj (inr (Data (fnode t)))) e1) e0) e))) eqn:Eql,
(exprD' tus tvs (typtree typ)
     (App (App (App (Inj (inr (Data (fnode t)))) e1) e0)
        (set_reif i vr e typ))) eqn :Eqr; auto.
autorewrite with exprD_rw in *; simpl in *;
forward; inv_some.
autorewrite with exprD_rw in H3. simpl in H3.
forward. 
clear e13 e9 e11.
autorewrite with exprD_rw in H4. simpl in H4. forward.
assert (X := ExprTac.exprD_typeof_Some _ _ _ _ _ H8).
eapply ExprTac.exprD_typeof_eq in X; auto with typeclass_instances.
Focus 2. apply H0. inv X. 
rewrite H0 in H8. inv H8.
 fold OpenT in H3. fold exprT in H3. 
assert (t = t1). apply ExprTac.exprD_typeof_Some in H3; try apply _.
simpl in H3. unfold typeof_func_opt in H3. simpl in H3. inv H3. auto.
subst.
unfold exprT in e2. simpl in e2.
assert (X := set_denote i~1 t1 tus tvs). fold func in *.
rewrite X in H3. inv H3. clear X.
unfold exprT_App. simpl.
autorewrite with exprD_rw in H0.
simpl in H0. forward. inv H7.
autorewrite with exprD_rw in H3.
simpl in H3. forward.
autorewrite with exprD_rw in H7.
simpl in H7.
unfold funcAs in H7. simpl (typeof_sym (inr (Data (fnode t1)))) in H7.
unfold typeof_func_opt in H7. simpl (typeof_func (Data (fnode t1))) in H7.
inv_some.
rewrite type_cast_refl in H7. simpl in H7. inv_some. 
unfold exprT_App. simpl.  
specialize (IHi tus tvs t1 vr e). rewrite <- IHi in H1.
f_equal.
p_exprD H1.
unfold exprT_App. simpl.
p_exprD H5. p_exprD H5. simpl in *.
unfold funcAs in H4. simpl (typeof_sym (inr (Data (fset t1 i)))) in H4.
unfold typeof_func_opt in H4.
unfold typeof_func in H4. unfold typeof_data in H4.
rewrite type_cast_refl in H4. unfold Rcast in H4.
simpl in H4. inv_some.
unfold exprT_App. simpl.
rewrite H6 in H9.
rewrite H7 in H11.
inv_some. auto. apply _. apply _.

autorewrite with exprD_rw in *; simpl in *;
forward; inv_some.
autorewrite with exprD_rw in H3. simpl in H3.
forward. 
autorewrite with exprD_rw in H4. simpl in H4. forward. 
Admitted.
(*assert (X := ExprTac.exprD_typeof_Some _ _ _ _ _ H8).
eapply ExprTac.exprD_typeof_eq in X; auto with typeclass_instances.
Focus 2. apply H0. inv X. 
rewrite H0 in H8. inv H8.
 fold OpenT in H3. fold exprT in H3. 
assert (t = t1). apply ExprTac.exprD_typeof_Some in H3; try apply _.
simpl in H3. unfold typeof_func_opt in H3. simpl in H3. inv H3. auto.
subst.
unfold exprT in e2. simpl in e2.
assert (X := set_denote i~1 t1 tus tvs). fold func in *.
rewrite X in H3. inv H3. clear X.
unfold exprT_App. simpl.
autorewrite with exprD_rw in H0.
simpl in H0. forward. inv H7.
autorewrite with exprD_rw in H3.
simpl in H3. forward.
autorewrite with exprD_rw in H7.
simpl in H7.
unfold funcAs in H7. simpl (typeof_sym (inr (Data (fnode t1)))) in H7.
unfold typeof_func_opt in H7. simpl (typeof_func (Data (fnode t1))) in H7.
inv_some.
rewrite type_cast_refl in H7. simpl in H7. inv_some. 
unfold exprT_App. simpl.  
specialize (IHi tus tvs t1 vr e). rewrite <- IHi in H1.
f_equal.
p_exprD H1.
unfold exprT_App. simpl.
p_exprD H5. p_exprD H5. simpl in *.
unfold funcAs in H4. simpl (typeof_sym (inr (Data (fset t1 i)))) in H4.
unfold typeof_func_opt in H4.
unfold typeof_func in H4. unfold typeof_data in H4.
rewrite type_cast_refl in H4. unfold Rcast in H4.
simpl in H4. inv_some.
unfold exprT_App. simpl.
rewrite H6 in H9.
rewrite H7 in H11.
inv_some. auto. apply _. apply _.


assert (exists v, exprD' tus tvs (typtree typ)
          (App (App (App (Inj (inr (Data (fnode t)))) e1) e0)
             (set_reif i vr e typ)) = Some v ).
p_exprD Eql.
p_exprD H1. 
p_exprD H1.
p_exprD H2.
p_exprD H0.
eexists.
autorewrite with exprD_rw. simpl.
match goal with
[ |- match ?x with _ => _ end = _ ] => destruct x eqn:?
end.
autorewrite with exprD_rw. simpl. forward.
autorewrite with exprD_rw. simpl. forward.
autorewrite with exprD_rw. simpl. forward.
Opaque type_cast.
(*unfold funcAs.
simpl. inv_some. simpl.
p_exprD H7. unfold funcAs in H7; simpl in H7.
specialize (IHi tus tvs t vr e).
rewrite <- IHi in *.*)
Print set_reif.

            
            solve_funcAs H6.
            destruct (type_cast
           (tyArr (typtree t0)
              (tyArr (tyoption t0) (tyArr (typtree t0) (typtree t0))))
           (tyArr t4 (tyArr t3 (tyArr t1 (typtree t))))); inv H6.
            solve_funcAs H4.
                                                                              
            unfold funcAs in H4.
            simpl in H4. 
            edestruct IHi. eauto. 
            autorewrite with exprD_rw in *. simpl in *.
destruct (
            destruct (exprD' tus tvs (typtree t) (node e2 e1 (set_reif i vr e0 t) t0)) eqn : ?.  eauto. assert False; [ | contradiction].
            



assert (e4 = e8).
destruct (exprD_ex_typs  _ _ _ _ _ _ Eql).
destruct H.
destruct (exprD_ex_typs  _ _ _ _ _ _ Eqr).
destruct H1.
wforward.
autorewrite with expr_rw.


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
Admitted. *)

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