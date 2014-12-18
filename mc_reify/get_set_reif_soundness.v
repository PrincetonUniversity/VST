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
        [ H : ?x = Some _, H2 : ?x = Some _ |- _ ] => rewrite H in H2; inv_some
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
       | [ H : exprD' _ _ _ (App _ _ ) = (*Some*) _ |- _ ] => p_exprD H
       | [ H : context [match exprD' _ _ _ (App _ _) with _ => _ end] |- _] =>
         p_exprD H
    end; 
  cleanup_dups; subst_rty; inv_same_types).

Ltac solve_funcAs :=
repeat
match goal with 
| [ H : context [funcAs _ _] |- _ ]  =>  unfold funcAs in H; simpl in H;  rewrite type_cast_refl in H; unfold Rcast, Relim in H; simpl in H
| [ |- context [funcAs _ _ ] ]=> unfold funcAs; simpl; try rewrite type_cast_refl; unfold Rcast, Relim; simpl
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
| [ H : exprD' ?tus ?tvs ?t (Inj ?e ) = Some ?val |- _ ] =>
let X := fresh "X" in
     (assert (X := exprD_typeof_Some tus tvs t (Inj e) val);
     simpl in X; specialize (X H); inv X); 
       p_exprD H; ( solve_funcAs || fail)
| [ H : context [match exprD' ?tus ?tvs ?t (Inj ?e ) with _ => _ end] |- _ ] =>
       p_exprD H; ( solve_funcAs || fail)
| [ H : exprD' ?tus ?tvs ?t (Inj ?e ) = _ |- _ ] =>
       p_exprD H; ( solve_funcAs || fail)
end; unfold Rcast in *; simpl in *; inv_some; subst_rty);
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

Ltac pose_types :=
             repeat
             match goal with
               | [ H : exprD' ?tus ?tvs ?ty ?v = Some _  |- _ ] =>
                   match goal with
                     | [H' : typeof_expr tus tvs v = Some ty |- _ ] => fail 1
                     | _ => let X := fresh "H" in 
                             assert (X := exprD_typeof_Some tus tvs ty _ _ H)
                   end
             end.  


Ltac solve_exprD :=
repeat (
             p_exprD_app; p_exprD_inj;
             autorewrite with exprD_rw; simpl; solve_funcAs; try solve [auto with typeclass_instances | reflexivity]; try congruence; pose_types; pose_exprD'; fold func in *; forward; try (rewrite type_cast_refl in *; unfold Rcast, Relim; simpl in *)). 

Opaque type_cast.

Lemma set_reif_istree :
  forall i tus tvs t0 vr e t x,
    exprD' tus tvs t0 (set_reif i vr e t) = Some x ->
    t0 = typtree t.
Proof.
simpl in *.
induction i; intros; simpl in *; unfold leaf, node, some_reif, none_reif in *.
  + destruct (as_tree e) eqn:?; destruct_as_tree; 
      [ apply (as_tree_l) in Heqo | apply as_tree_r in Heqo | ]; subst; 
      solve_exprD; specialize (IHi tus tvs (typtree t1)); eapply IHi in H1; auto.
  + destruct (as_tree e) eqn:?; destruct_as_tree; 
      [ apply (as_tree_l) in Heqo | apply as_tree_r in Heqo | ]; subst; 
      solve_exprD; specialize (IHi tus tvs (typtree t1)); 
      try eapply IHi in H5; try eapply IHi in H3; auto.
  + destruct (as_tree e) eqn:?; destruct_as_tree; 
      [ apply (as_tree_l) in Heqo | apply as_tree_r in Heqo | ]; subst; 
      solve_exprD.
Admitted. (*Qed*)
     

Lemma set_reif_exprD :
forall tus tvs typ i vr e v ev,
exprD' tus tvs (typtree typ) e = Some ev ->
exprD' tus tvs typ vr = Some v ->
exists r, exprD' tus tvs (typtree typ) (set_reif i vr e typ) = Some r.
Proof.
induction i; intros; simpl in *; unfold leaf, node, some_reif, none_reif in *;
    (destruct (as_tree e) eqn:?; destruct_as_tree; 
      [ apply (as_tree_l) in Heqo | apply as_tree_r in Heqo | ]); subst; 
      solve_exprD; eauto.
  + edestruct (IHi vr e0); eauto; solve_exprD; eauto. 
  + edestruct (IHi vr (Inj (inr (Data (fleaf typ))))); eauto; solve_exprD; eauto.  + edestruct (IHi vr e2); eauto; solve_exprD; eauto.
  + edestruct (IHi vr (Inj (inr (Data (fleaf typ))))); eauto; solve_exprD; eauto.
Admitted. (*Qed.*)

Lemma set_reif_vr : forall tus tvs typ i e vr e4,
  exprD' tus tvs (typtree typ) (set_reif i vr e typ) = Some e4 ->
  exists v, exprD' tus tvs typ vr = Some v.
Proof.
induction i; intros; simpl in *; unfold leaf, node, some_reif, none_reif in *;
    (destruct (as_tree e) eqn:?; destruct_as_tree; 
      [ apply (as_tree_l) in Heqo | apply as_tree_r in Heqo | ]); subst; 
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
pose_types.
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
repeat (solve_exprD;
        try set_reif_ex;
        extract_set_reif_type;
        try set_typeof_None;
        try (progress get_vr_type; pose_types)).



Lemma set_reif_eq2 :
forall i tus tvs typ vr tr val,
exprD' tus tvs (typtree typ) tr = Some val ->
exprD' tus tvs (typtree typ) (App (App (Inj (inr (Data (fset typ i)))) vr) tr)  =
exprD' tus tvs (typtree typ) (set_reif i vr tr typ).
Proof. 
induction i; intros.
   + destruct (exprD' tus tvs (typtree typ)
     (App (App (Inj (inr (Data (fset typ i~1)))) vr) tr)) eqn:?,
     (exprD' tus tvs (typtree typ) (set_reif i~1 vr tr typ)) eqn:?; auto; 
     simpl in *; unfold node, leaf, some_reif, none_reif in *;
     simpl in *; (destruct (as_tree tr) eqn:?; destruct_as_tree; [apply as_tree_l in Heqo1 | apply as_tree_r in Heqo1 | ]); subst; solve_exprD; unfold exprT_App; simpl; set_reif_tac.
         * specialize (IHi tus tvs t0). erewrite <- IHi in *; eauto.
           solve_exprD.
         * specialize (IHi tus tvs t0). erewrite <- IHi in *; eauto;
           solve_exprD.
    + destruct (exprD' tus tvs (typtree typ)
     (App (App (Inj (inr (Data (fset typ i~0)))) vr) tr)) eqn :?,
       (exprD' tus tvs (typtree typ) (set_reif i~0 vr tr typ)) eqn:?;
     auto;
     simpl in *; unfold node, leaf, some_reif, none_reif in *;
     simpl in *; (destruct (as_tree tr) eqn:?; destruct_as_tree; [apply as_tree_l in Heqo1 | apply as_tree_r in Heqo1 | ]); subst; solve_exprD; unfold exprT_App; simpl; set_reif_tac.
         * specialize (IHi tus tvs t0). erewrite <- IHi in *; eauto.
           solve_exprD.
         * specialize (IHi tus tvs t0). erewrite <- IHi in *; eauto;
           solve_exprD.
     + destruct (exprD' tus tvs (typtree typ)
     (App (App (Inj (inr (Data (fset typ 1)))) vr) tr)) eqn :?,
                (exprD' tus tvs (typtree typ) (set_reif 1 vr tr typ)) eqn:?;
                 auto;
     simpl in *; unfold node, leaf, some_reif, none_reif in *;
     simpl in *; (destruct (as_tree tr) eqn:?; destruct_as_tree; [apply as_tree_l in Heqo1 | apply as_tree_r in Heqo1 | ]); subst; solve_exprD; unfold exprT_App; simpl; set_reif_tac.
Qed. (*THIS MIGHT TAKE FOREVER*)
 _exprD H4. solve_funcAs. 
match goal with
end.

         *
match goal with 

end. set_reif_tac.

Ltac p_exprD_app' :=
  repeat
    (match goal with
       | [ H : exprD' _ _ _ (App _ _ ) = (*Some*) _ |- _ ] => p_exprD H
    end; 
  cleanup_dups; subst_rty; inv_same_types).
p_exprD_app'. solve_exprD.

solve_exprD.

    
repeat match type of Heqo0 with
             | match ?x with _ => _ end = _ => destruct x eqn:?
           end; try congruence; set_reif_tac. 
         * repeat (match goal with
             | [ H : match ?x with _ => _ end = _ |- _] => destruct x eqn:?
           end; try congruence;  set_reif_tac).
         * repeat (match goal with
             | [ H : match ?x with _ => _ end = _ |- _] => destruct x eqn:?
           end; try congruence).  
             - set_reif_tac.
             - set_reif_tac; repeat (match goal with
             | [ H : match ?x with _ => _ end = _ |- _] => destruct x eqn:?
           end; try congruence; set_reif_tac). fold func in *. congruence.
             - set_reif_tac; repeat (match goal with
             | [ H : match ?x with _ => _ end = _ |- _] => destruct x eqn:?
           end; try congruence; set_reif_tac). 
             - set_reif_tac; repeat (match goal with
             | [ H : match ?x with _ => _ end = _ |- _] => destruct x eqn:?
           end; try congruence; set_reif_tac). 
               rewrite type_cast_refl in *; try congruence; apply _.
             - rewrite type_cast_refl in *; try congruence; try apply _.
         * repeat (match goal with
             | [ H : match ?x with _ => _ end = _ |- _] => destruct x eqn:?
           end; try congruence;  set_reif_tac).
  + admit.
  + simpl.



set_reif_tac).
 pose_types. 
 p_exprD_inj. congruence.
admit. rewrite type_cast_refl in *; try congruence. apply _. apply _.
rewrite type_cast_refl in *; try congruence; apply _.
  * 

(*set_reif_vr*)eapply set_reif_vr in H8.
repeat match goal with
             | [ H : match ?x with _ => _ end = _ |- _] => destruct x eqn:?
           end; try congruence; set_reif_tac'.
      eapply typeof_set_reif_None_F in Heqo; ; try contradiction. 
* solve_exprD.

  



set_typeof_None.

Ltac pose_exprD'' :=
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
      | [ H : typeof_expr ?tus ?tvs ?v = None  |- _ ] =>
        match goal with
          | [H' : exprD' tus tvs t v = None |- _ ] => fail 1
          | _ => match type of H with
                   | ?x => let X := fresh "H" in 
                       assert x as X by exact H; 
                       rewrite (ExprFacts.exprD'_typeof_expr tus tvs v t) in X;
                       destruct X
                 end
        end
    end.

             - 
set_reif_tac'.

set_reif_tac.

solve_exprD.
               p_exprD H8.
               unfold funcAs in H8.
               simpl in H8.

pose_exprD'. 


match goal with
[ 
               rewrite ExprFacts.exprD'_typeof_expr in Heqo.
SearchAbout typeof_expr.
               rewrite type
fold func in *. try congruence.

         



(*old starts here *) induction i;
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
       destruct (exprD' tus tvs (typtree typ)
     (App (App (Inj (inr (Data (fset typ i~1)))) vr)
        (Inj (inr (Data (fleaf typ)))))) eqn :?,
                (exprD' tus tvs (typtree typ)
     (node (leaf typ) (none_reif typ) (set_reif i vr (leaf typ) typ) typ)) eqn:?.
         * unfold node, leaf, none_reif in *.
           p_exprD_app; p_exprD_inj.
           unfold exprT_App. simpl.
           specialize (IHi tus tvs t0). erewrite <- IHi in H1; eauto.
           p_exprD_app; p_exprD_inj.
           unfold exprT_App. simpl. auto.
           autorewrite with exprD_rw. simpl. unfold funcAs. 
           simpl. rewrite type_cast_refl. simpl. reflexivity.
           apply _. 
         * unfold node, leaf, none_reif in *.
           p_exprD_app; p_exprD_inj.
           repeat match type of Heqo0 with
             | match ?x with _ => _ end = _ => destruct x eqn:?
           end; try congruence. 
           p_exprD_app. p_exprD_inj.
           rewrite ExprFacts.exprD'_typeof_expr in Heqo.
           fold func in *. destruct Heqo. congruence.
                      rewrite ExprFacts.exprD'_typeof_expr in Heqo.
           fold func in *. destruct Heqo. 
           apply set_reif_istree in H0. subst.           
           p_exprD_app; p_exprD_inj.
           do 2 (p_exprD Heqo1;
           unfold funcAs in *; simpl in *;
           try rewrite type_cast_refl in *).
           rewrite type_cast_refl in *. simpl in *.
           congruence.
           apply _. apply _. apply _. apply _.
           edestruct (set_reif_exprD tus tvs t).
           instantiate (2 := (Inj (inr (Data (fleaf t))))).
           autorewrite with exprD_rw. simpl. 
           unfold funcAs in *; simpl in *; try rewrite type_cast_refl in *.
           reflexivity.
           apply _.
           eauto.
           instantiate (1:= i) in H0.
           assert (X := exprD_typeof_Some tus tvs (typtree t)  _ _ H0).
           fold func in *. congruence.
         * unfold node, leaf, none_reif in *.
           p_exprD_app; p_exprD_inj.
           Check set_reif_vr.
           edestruct (set_reif_vr tus tvs typ _ _ _ _ H1).
           fold func in *.
           
          pose_types. 
          fold func in *. rewrite H2 in *. rewrite H0 in *.
          p_exprD H5.
          solve_funcAs. inv H3. apply _.
        * auto.
  +
           
           
SearchAbout typeof_expr.
           eapply AppN.type_of_applys_typeof_None in Heqo.
           
SearchAbout typeof_expr.

           simpl in Heqo1.
           p_exprD Heqo1.
           
           

           destruct Heqo.
           rewrite 
           edestruct (set_reif_exprD tus tvs t i vr).
           instantiate (2 := (Inj (inr (Data (fleaf t))))).
           autorewrite with exprD_rw; forward. simpl.
           unfold funcAs. simpl. rewrite type_cast_refl.
           reflexivity. apply _. eauto.
           fold func in *.
           congruence.
           p_exprD_app.
           p_exprD Heqo1.
           p_exprD Heqo1.
           apply 
           congruence.
           rewrite exprD
           repeat (autorewrite with exprD_rw in Heqo0; simpl in Heqo0; forward; inv_some). unfold funcAs in Heqo0. simpl in Heqo0. rewrite type_cast_refl in Heqo0.
inversion Heqo0.
           
           destruct (typeof_expr tus tvs
              (set_reif i vr (Inj (inr (Data (fleaf t)))) t)).
           
           specialize (IHi tus tvs typ vr 
                           (Inj (inr (Data (fleaf typ)))) _ H0).
           p_exprD_inj.
           repeat (autorewrite with exprD_rw in IHi; simpl in IHi;
           forward; inv_some). unfold funcAs in IHi; simpl in IHi.
           rewrite type_cast_refl in IHi. simpl in IHi.
           rewrite type_cast_refl in IHi. simpl in IHi.
           unfold exprT_App in IHi. simpl in IHi.
           
       
       
        
        
 

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