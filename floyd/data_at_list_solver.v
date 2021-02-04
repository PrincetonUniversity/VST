Require Import VST.floyd.base2.
Require Export VST.floyd.Zlength_solver.
Require Export VST.floyd.list_solver.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.entailer.
Require Import VST.floyd.field_compat.

(** * list extensionality *)
(* To prove equality between two lists, a convenient way is to apply extensionality
  and prove their length are equal and each corresponding entries are equal.
  It is convenient because then we can use Znth_solve to solve it. *)

Definition data_subsume {cs : compspecs} (t : type) (x y : reptype t) : Prop :=
  forall sh p, data_at sh t x p |-- data_at sh t y p.

Lemma data_subsume_refl : forall {cs : compspecs} (t : type) (x : reptype t),
  data_subsume t x x.
Proof. unfold data_subsume. intros. auto. Qed.

Lemma data_subsume_refl' : forall {cs : compspecs} (t : type) (x x' : reptype t),
  x = x' ->
  data_subsume t x x'.
Proof. unfold data_subsume. intros. cancel. Qed.

Lemma data_subsume_default : forall {cs : compspecs} (t : type) (x y : reptype t),
  y = default_val t ->
  data_subsume t x y.
Proof. unfold data_subsume. intros. subst y. apply data_at_data_at_. Qed.

#[export] Hint Resolve data_subsume_refl data_subsume_refl' data_subsume_default : core.

Lemma data_subsume_array_ext : forall {cs : compspecs} (t : type) (n : Z) (al bl : list (reptype t)),
  n = Zlength al ->
  n = Zlength bl ->
  (forall (i : Z), 0 <= i < n -> data_subsume t (Znth i al) (Znth i bl)) ->
  data_subsume (tarray t n) al bl.
Proof.
  intros.
  generalize dependent bl.
  generalize dependent n.
  induction al; intros; destruct bl as [ | b bl];
    autorewrite with list_solve_rewrite in *; Zlength_simplify_in_all; try Zlength_solve;
    unfold data_subsume; intros.
  - (* al = [] /\ bl = [] *)
    entailer!.
  - (* al <> [] /\ bl <> [] *)
    do 2 rewrite split2_data_at_Tarray_app with (mid := 1) by Zlength_solve.
    apply sepcon_derives.
    + specialize (H1 0 ltac:(Zlength_solve)).
      autorewrite with Znth in H1.
      rewrite data_at_singleton_array_eq with (v := a) by auto.
      rewrite data_at_singleton_array_eq with (v := b) by auto.
      apply H1.
    + apply IHal; try Zlength_solve.
      intros. specialize (H1 (i+1) ltac:(Zlength_solve)).
      autorewrite with Znth in H1.
      Zlength_simplify_in H1.
      replace (i + 1 - 1) with i in H1 by lia.
      apply H1.
Qed.

Ltac simpl_reptype :=
  repeat lazymatch goal with
  | |- context [reptype ?t] =>
    let T' := eval compute in (reptype t) in
    change (reptype t) with T' in *
  | H : context [reptype ?t] |- _ =>
    let T' := eval compute in (reptype t) in
    change (reptype t) with T' in *
  end.

(* Tactic apply_list_ext applies the proper extensionality lemma and proves
  the lengths are the same and reduces the goal to relation between entries. *)
Ltac apply_list_ext ::=
  first
  [ apply data_subsume_array_ext;
    simpl_reptype;
    only 1, 2 : Zlength_solve
  | match goal with |- @eq ?list_A _ _ =>
      match eval compute in list_A with list ?A =>
        apply (@Znth_eq_ext A ltac:(auto with typeclass_instances))
      end
    end;
    only 1 : Zlength_solve
  | match goal with |- @Forall ?A ?P ?l =>
      rewrite Forall_Znth;
      intros
    end
  | match goal with |- @forall_range ?A ?d ?lo ?hi ?l ?P =>
      rewrite <- forall_range_fold;
      intros
    end
  ];
  Zlength_simplify;
  intros.

Ltac list_solve_preprocess ::=
  fold_Vbyte;
  simpl_reptype;
  autounfold with list_solve_unfold in *;
  autorewrite with list_solve_rewrite in *;
  repeat match goal with [ |- _ /\ _ ] => split end;
  intros.

