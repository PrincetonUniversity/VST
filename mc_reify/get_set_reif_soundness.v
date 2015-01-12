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
| [ H : match ?x with _ => _  end = _ |- _ ] => destruct x; simpl in H;  try congruence end. 
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

Ltac solve_exprD := solve_exprD.solve_exprD tbl.

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
      solve_exprD; specialize (IHi tus tvs (typtree t1));
      eapply IHi in H1; auto.
  + destruct (as_tree e) eqn:?; destruct_as_tree; 
      [ apply (as_tree_l) in Heqo | apply as_tree_r in Heqo | ]; subst; 
      solve_exprD; specialize (IHi tus tvs (typtree t1)); 
      try eapply IHi in H5; try eapply IHi in H3; auto.
  + destruct (as_tree e) eqn:?; destruct_as_tree; 
      [ apply (as_tree_l) in Heqo | apply as_tree_r in Heqo | ]; subst; 
      solve_exprD.
Time Qed.
(*Admitted. (*Qed*)*)
     

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
+ edestruct (IHi vr e0); eauto; solve_exprD; eauto. rewrite H8.
Unset Ltac Debug.
fold func in *. 
Set Printing Implicit.
Print solve_exprD.tbl.
assert (X := exprD_typeof_Some tus tvs (typtree typ) ((set_reif i vr e0 typ)) x H5).
pose_types.
(*pose_types. *)
(*Unset Ltac Debug.
Set Printing Implicit.
Check RSym_sym.
Locate RSym_sym.
assert (X := exprD_typeof_Some tus tvs (typtree typ) ((set_reif i vr e0 typ)) x H5).
 fold func in *. pose_types.*)
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
(*induction i; intros.
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
     simpl in *; (destruct (as_tree tr) eqn:?; destruct_as_tree; [apply as_tree_l in Heqo1 | apply as_tree_r in Heqo1 | ]); subst; solve_exprD; unfold exprT_App; simpl; set_reif_tac. *)
Admitted.

(*
induction i; intros.
   + Time destruct (exprD' tus tvs (typtree typ)
     (App (App (Inj (inr (Data (fset typ i~1)))) vr) tr)) eqn:?,
     (exprD' tus tvs (typtree typ) (set_reif i~1 vr tr typ)) eqn:?; auto;
     simpl in *; unfold node, leaf, some_reif, none_reif in *;
     simpl in *; abstract (destruct (as_tree tr) eqn:?; destruct_as_tree; [apply as_tree_l in Heqo1 | apply as_tree_r in Heqo1 | ]; subst;
abstract (solve_exprD; unfold exprT_App; simpl; set_reif_tac; try ( specialize (IHi tus tvs t0); erewrite <- IHi in *; eauto; solve_exprD))). 
abstract (solve_exprD; unfold exprT_App; simpl; set_reif_tac; try ( specialize (IHi tus tvs t0); erewrite <- IHi in *; eauto; solve_exprD)).
abstract (solve_exprD; unfold exprT_App; simpl; set_reif_tac; try ( specialize (IHi tus tvs t0); erewrite <- IHi in *; eauto; solve_exprD)).
abstract (solve_exprD; unfold exprT_App; simpl; set_reif_tac; try ( specialize (IHi tus tvs t0); erewrite <- IHi in *; eauto; solve_exprD)).
abstract (solve_exprD; unfold exprT_App; simpl; set_reif_tac; try ( specialize (IHi tus tvs t0); erewrite <- IHi in *; eauto; solve_exprD)).
abstract (solve_exprD; unfold exprT_App; simpl; set_reif_tac; try ( specialize (IHi tus tvs t0); erewrite <- IHi in *; eauto; solve_exprD)).
abstract (solve_exprD; unfold exprT_App; simpl; set_reif_tac; try ( specialize (IHi tus tvs t0); erewrite <- IHi in *; eauto; solve_exprD)).
abstract (solve_exprD; unfold exprT_App; simpl; set_reif_tac; try ( specialize (IHi tus tvs t0); erewrite <- IHi in *; eauto; solve_exprD)).
abstract (solve_exprD; unfold exprT_App; simpl; set_reif_tac; try ( specialize (IHi tus tvs t0); erewrite <- IHi in *; eauto; solve_exprD)).
abstract (solve_exprD; unfold exprT_App; simpl; set_reif_tac; try ( specialize (IHi tus tvs t0); erewrite <- IHi in *; eauto; solve_exprD)).
abstract (solve_exprD; unfold exprT_App; simpl; set_reif_tac; try ( specialize (IHi tus tvs t0); erewrite <- IHi in *; eauto; solve_exprD)).
abstract (solve_exprD; unfold exprT_App; simpl; set_reif_tac; try ( specialize (IHi tus tvs t0); erewrite <- IHi in *; eauto; solve_exprD)).
abstract (solve_exprD; unfold exprT_App; simpl; set_reif_tac; try ( specialize (IHi tus tvs t0); erewrite <- IHi in *; eauto; solve_exprD)).
abstract (solve_exprD; unfold exprT_App; simpl; set_reif_tac; try ( specialize (IHi tus tvs t0); erewrite <- IHi in *; eauto; solve_exprD)).
abstract (solve_exprD; unfold exprT_App; simpl; set_reif_tac; try ( specialize (IHi tus tvs t0); erewrite <- IHi in *; eauto; solve_exprD)).

subst; solve_exprD; unfold exprT_App; simpl; set_reif_tac; try ( specialize (IHi tus tvs t0); erewrite <- IHi in *; eauto; solve_exprD).
           solve_exprD.
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

Lemma get_reif_eq2 :
forall typ i tr tbl,
reflect tbl nil nil (App (Inj (inr (Data (fget typ i)))) tr) (tyoption typ) =
reflect tbl nil nil (get_reif i tr) (tyoption typ).
Proof.
Admitted. *)

End tbled.