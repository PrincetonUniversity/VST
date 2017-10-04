Require Import ZArith Coq.Lists.List Permutation.
Require Import VST.msl.Axioms.
Require Import VST.msl.predicates_sa.
Require Import veristar.variables veristar.datatypes veristar.clauses
               veristar.list_denote veristar.heapresolve
               veristar.model_type veristar.model.

Module Type SUBST_SOUND.
Declare Module VSD: VERISTAR_DEFS.
Import VSD VeriStarModel.

Axiom subst_expr_sound : forall i e e' s,
  (subst_expr i e e' ==
   match e' with Nil => Nil | Var x  => if Var.eq_dec i x then e else e'
   end) s.

Axiom subst_space_sound : forall i e a,
  space_atom_denote (subst_space i e a) =
  match a with
  | Next x y => space_atom_denote (Next (subst_expr i e x) (subst_expr i e y))
  | Lseg x y => space_atom_denote (Lseg (subst_expr i e x) (subst_expr i e y))
  end.

Axiom subst_list_denote_sound :
  forall A Q (l : list A) (denote: A -> spred) (subst: A -> A) B,
  list_denote denote Q B (map subst l) =
  match map subst l with
  | nil => B
  | _ :: _ => list_denote denote Q B (map subst l)
  end.

Axiom subst_list_denote_sound_space : forall (l : list space_atom) i e,
  list_denote space_atom_denote sepcon emp (map (subst_space i e) l) =
  match map (subst_space i e) l with
  | nil => emp
  | _ :: _ => list_denote space_atom_denote sepcon emp (map (subst_space i e) l)
  end.

Axiom subst_list_denote_sound_intersection : forall (l : list pure_atom) i e B,
  list_denote pure_atom_denote (@andp state) B (map (subst_pure i e) l) =
  match map (subst_pure i e) l with
  | nil => B
  | _ :: _ => list_denote pure_atom_denote (@andp state) B (map (subst_pure i e) l)
  end.

Axiom subst_pures_denote_sound_intersection : forall (l : list pure_atom) i e B,
  list_denote pure_atom_denote (@andp state) B (subst_pures i e l) =
  match map (subst_pure i e) l with
  | nil => B
  | _ :: _ => list_denote pure_atom_denote (@andp state) B (subst_pures i e l)
  end.

Axiom subst_list_denote_sound_union : forall (l : list pure_atom) i e B,
  list_denote pure_atom_denote (@orp state) B (map (subst_pure i e) l) =
  match map (subst_pure i e) l with
  | nil => B
  | _ :: _ => list_denote pure_atom_denote (@orp state) B (map (subst_pure i e) l)
  end.

Axiom subst_pures_denote_sound_union : forall (l : list pure_atom) i e B,
  list_denote pure_atom_denote (@orp state) B (subst_pures i e l) =
  match map (subst_pure i e) l with
  | nil => B
  | _ :: _ => list_denote pure_atom_denote (@orp state) B (subst_pures i e l)
  end.

Axiom subst_list_denote_sound0 : forall {A} (Q : spred -> spred -> spred) (l : list A)
  (denote: A -> spred) (subst: A -> A) (B:spred),
  list_denote denote Q B (map subst l) =
  match l with
  | nil => B
  | x :: t => Q (denote (subst x)) (list_denote denote Q B (map subst t))
  end.

Axiom subst_list_denote_sound_space0 : forall (l : list space_atom) i e,
  list_denote space_atom_denote sepcon emp (map (subst_space i e) l) =
  match l with
  | nil => emp
  | x :: t => sepcon (space_atom_denote (subst_space i e x))
    (list_denote space_atom_denote sepcon emp (map (subst_space i e) t))
end.

Axiom subst_list_denote_sound_intersection0 : forall (l : list pure_atom) i e B,
  list_denote pure_atom_denote (@andp state) B (map (subst_pure i e) l) =
  match l with
  | nil => B
  | x :: t => (@andp state) (pure_atom_denote (subst_pure i e x))
    (list_denote pure_atom_denote (@andp state) B (subst_pures i e t))
end.

Axiom subst_list_denote_sound_union0 : forall (l : list pure_atom) i e B,
  list_denote pure_atom_denote (@orp state) B (map (subst_pure i e) l) =
  match l with
  | nil => B
  | x :: t => (@orp state) (pure_atom_denote (subst_pure i e x))
    (list_denote pure_atom_denote (@orp state) B (subst_pures i e t))
end.

Axiom subst_spaces_sound: forall AL i e,
  space_denote (map (subst_space i e) AL)  =
  list_denote (fun a => space_atom_denote (subst_space i e a)) sepcon emp AL.

Axiom subst_pure_sound: forall i e a,
  pure_atom_denote (subst_pure i e a) =
  match a with Eqv e1 e2 => pure_atom_denote (Eqv (subst_expr i e e1) (subst_expr i e e2))
  end.

Axiom subst_pures_inter_sound: forall P i e B,
  list_denote pure_atom_denote (@andp state) B (map (subst_pure i e)P) =
  list_denote (fun a => pure_atom_denote (subst_pure i e a)) (@andp state) B P.

Axiom subst_pures_union_sound: forall P i e B,
  list_denote pure_atom_denote (@orp state) B (map (subst_pure i e)P) =
  list_denote (fun a => pure_atom_denote (subst_pure i e a)) (@orp state) B P.

Axiom subst_clause_sound: forall cl i e,
  clause_denote (subst_clause i e cl) =
  match cl with
  | PureClause pa pa' _ _ =>
      clause_denote (mkPureClause (subst_pures_delete i e pa) (subst_pures i e pa'))
  | NegSpaceClause pa sa pa' =>
      clause_denote (NegSpaceClause (subst_pures_delete i e pa) (subst_spaces i e sa) (subst_pures i e pa'))
  | PosSpaceClause pa pa' sa' =>
      clause_denote (PosSpaceClause (subst_pures_delete i e pa) (subst_pures i e pa') (subst_spaces i e sa'))
  end.

Axiom expr_cmp_eq: forall e e',
  expr_cmp e e' = Eq -> (e == e') = TT.

Axiom expr_cmp_eq': forall e e' s,
  expr_cmp e e' = Eq -> (e == e') s.

Axiom remove_trivial_atoms_correct : forall pcs B,
  list_denote pure_atom_denote (@andp state) B pcs =
  list_denote pure_atom_denote (@andp state) B (remove_trivial_atoms pcs).

Axiom subst_pures_delete_same : forall i e pcs B,
  list_denote pure_atom_denote (@andp state) B (subst_pures_delete i e pcs) =
  list_denote pure_atom_denote (@andp state) B (subst_pures i e pcs).

Axiom clause_denote_PureClause_sound: forall i e Gamma Delta,
  clause_denote (mkPureClause (subst_pures_delete i e Gamma) Delta) =
  clause_denote (mkPureClause (subst_pures i e Gamma) Delta).

Axiom clause_denote_NegSpaceClause_sound: forall i e Gamma Sigma Delta,
  clause_denote (NegSpaceClause (subst_pures_delete i e Gamma) Sigma Delta) =
  clause_denote (NegSpaceClause (subst_pures i e Gamma) Sigma Delta).

Axiom clause_denote_PosSpaceClause_sound: forall i e Gamma Sigma Delta,
  clause_denote (PosSpaceClause (subst_pures_delete i e Gamma) Sigma Delta) =
  clause_denote (PosSpaceClause (subst_pures i e Gamma) Sigma Delta).

End SUBST_SOUND.

Module Subst_Sound (VSD: VERISTAR_DEFS) : SUBST_SOUND with Module VSD := VSD.
Module VSD := VSD.
Import VSD VeriStarModel.

(*Substitution Lemmas*)
Lemma subst_expr_sound : forall i e e' s,
  (subst_expr i e e' ==
   match e' with Nil => Nil | Var x  => if Var.eq_dec i x then e else e'
   end) s.
Proof.
intros; destruct e'; simpl.
reflexivity.
remember (Var.eq_dec i v) as b; destruct b; subst; reflexivity.
Qed.

Lemma subst_space_sound : forall i e a,
  space_atom_denote (subst_space i e a) =
  match a with
  | Next x y => space_atom_denote (Next (subst_expr i e x) (subst_expr i e y))
  | Lseg x y => space_atom_denote (Lseg (subst_expr i e x) (subst_expr i e y))
  end.
Proof.
intros; destruct a; try reflexivity.
Qed.

Lemma subst_list_denote_sound :
  forall A Q (l : list A) (denote: A -> spred) (subst: A -> A) B,
  list_denote denote Q B (map subst l) =
  match map subst l with
  | nil => B
  | _ :: _ => list_denote denote Q B (map subst l)
  end.
Proof.
induction l; simpl; intros; subst; reflexivity.
Qed.

Lemma subst_list_denote_sound_space : forall (l : list space_atom) i e,
  list_denote space_atom_denote sepcon emp (map (subst_space i e) l) =
  match map (subst_space i e) l with
  | nil => emp
  | _ :: _ => list_denote space_atom_denote sepcon emp (map (subst_space i e) l)
  end.
Proof.
intros; apply (subst_list_denote_sound space_atom sepcon _
  space_atom_denote (subst_space i e) emp).
Qed.

Lemma subst_list_denote_sound_intersection : forall (l : list pure_atom) i e B,
  list_denote pure_atom_denote (@andp state) B (map (subst_pure i e) l) =
  match map (subst_pure i e) l with
  | nil => B
  | _ :: _ => list_denote pure_atom_denote (@andp state) B (map (subst_pure i e) l)
  end.
Proof.
intros; apply (subst_list_denote_sound pure_atom (@andp state) _
  pure_atom_denote (subst_pure i e) B).
Qed.

Lemma subst_pures_denote_sound_intersection : forall (l : list pure_atom) i e B,
  list_denote pure_atom_denote (@andp state) B (subst_pures i e l) =
  match map (subst_pure i e) l with
  | nil => B
  | _ :: _ => list_denote pure_atom_denote (@andp state) B (subst_pures i e l)
  end.
Proof.
intros. apply subst_list_denote_sound_intersection.
Qed.

Lemma subst_list_denote_sound_union : forall (l : list pure_atom) i e B,
  list_denote pure_atom_denote (@orp state) B (map (subst_pure i e) l) =
  match map (subst_pure i e) l with
  | nil => B
  | _ :: _ => list_denote pure_atom_denote (@orp state) B (map (subst_pure i e) l)
  end.
Proof.
intros; apply (subst_list_denote_sound pure_atom (@orp state) _
  pure_atom_denote (subst_pure i e) B).
Qed.

Lemma subst_pures_denote_sound_union : forall (l : list pure_atom) i e B,
  list_denote pure_atom_denote (@orp state) B (subst_pures i e l) =
  match map (subst_pure i e) l with
  | nil => B
  | _ :: _ => list_denote pure_atom_denote (@orp state) B (subst_pures i e l)
  end.
Proof.
intros; apply subst_list_denote_sound_union.
Qed.

Lemma subst_list_denote_sound0 : forall {A} (Q : spred -> spred -> spred) (l : list A)
  (denote: A -> spred) (subst: A -> A) (B:spred),
  list_denote denote Q B (map subst l) =
  match l with
  | nil => B
  | x :: t => Q (denote (subst x)) (list_denote denote Q B (map subst t))
  end.
Proof.
induction l; simpl; intros; subst; reflexivity.
Qed.

Lemma subst_list_denote_sound_space0 : forall (l : list space_atom) i e,
  list_denote space_atom_denote sepcon emp (map (subst_space i e) l) =
  match l with
  | nil => emp
  | x :: t => sepcon (space_atom_denote (subst_space i e x))
    (list_denote space_atom_denote sepcon emp (map (subst_space i e) t))
end.
Proof.
intros; eapply (subst_list_denote_sound0).
Qed.

Lemma subst_list_denote_sound_intersection0 : forall (l : list pure_atom) i e B,
  list_denote pure_atom_denote (@andp state) B (map (subst_pure i e) l) =
  match l with
  | nil => B
  | x :: t => (@andp state) (pure_atom_denote (subst_pure i e x))
    (list_denote pure_atom_denote (@andp state) B (subst_pures i e t))
end.
Proof.
intros; apply (subst_list_denote_sound0).
Qed.

Lemma subst_list_denote_sound_union0 : forall (l : list pure_atom) i e B,
  list_denote pure_atom_denote (@orp state) B (map (subst_pure i e) l) =
  match l with
  | nil => B
  | x :: t => (@orp state) (pure_atom_denote (subst_pure i e x))
    (list_denote pure_atom_denote (@orp state) B (subst_pures i e t))
end.
Proof.
intros; apply (subst_list_denote_sound0).
Qed.

Lemma subst_spaces_sound: forall AL i e,
  space_denote (map (subst_space i e) AL)  =
  list_denote (fun a => space_atom_denote (subst_space i e a)) sepcon emp AL.
Proof.
induction AL; simpl; subst; intros.
  reflexivity.
rewrite <- (IHAL i e). clear IHAL.
reflexivity.
Qed.

Lemma subst_pure_sound: forall i e a,
  pure_atom_denote (subst_pure i e a) =
  match a with Eqv e1 e2 => pure_atom_denote (Eqv (subst_expr i e e1) (subst_expr i e e2))
  end.
Proof.
intros; destruct a; reflexivity.
Qed.

Lemma subst_pures_inter_sound: forall P i e B,
  list_denote pure_atom_denote (@andp state) B (map (subst_pure i e)P) =
  list_denote (fun a => pure_atom_denote (subst_pure i e a)) (@andp state) B P.
Proof.
induction P; simpl; subst; intros.
  reflexivity.
rewrite <- (IHP i e B). clear IHP.
rewrite subst_list_denote_sound_intersection. reflexivity.
Qed.

Lemma subst_pures_union_sound: forall P i e B,
  list_denote pure_atom_denote (@orp state) B (map (subst_pure i e)P) =
  list_denote (fun a => pure_atom_denote (subst_pure i e a)) (@orp state) B P.
Proof.
induction P; simpl; subst; intros.
  reflexivity.
rewrite <- (IHP i e B). clear IHP.
rewrite subst_list_denote_sound_union. reflexivity.
Qed.

Lemma subst_clause_sound: forall cl i e,
  clause_denote (subst_clause i e cl) =
  match cl with
  | PureClause pa pa' _ _ =>
      clause_denote (mkPureClause (subst_pures_delete i e pa) (subst_pures i e pa'))
  | NegSpaceClause pa sa pa' =>
      clause_denote (NegSpaceClause (subst_pures_delete i e pa) (subst_spaces i e sa) (subst_pures i e pa'))
  | PosSpaceClause pa pa' sa' =>
      clause_denote (PosSpaceClause (subst_pures_delete i e pa) (subst_pures i e pa') (subst_spaces i e sa'))
  end.
Proof.
intros; destruct cl; reflexivity.
Qed.

Lemma expr_cmp_eq: forall e e',
  expr_cmp e e' = Eq -> (e == e') = TT.
Proof.
intros.
extensionality s; apply prop_ext.
split; intros; trivial.
clear H0.
destruct e; simpl.
  destruct e'; simpl. reflexivity. inversion H.
  destruct e'; simpl. inversion H.
    inversion H.
symmetry in H. apply comp_eq in H; auto.
inversion H; subst; reflexivity.
Qed.

Lemma expr_cmp_eq': forall e e' s,
  expr_cmp e e' = Eq -> (e == e') s.
Proof.
intros.
rewrite (expr_cmp_eq _ _ H). trivial.
Qed.

Lemma remove_trivial_atoms_correct : forall pcs B,
  list_denote pure_atom_denote (@andp state) B pcs =
  list_denote pure_atom_denote (@andp state) B (remove_trivial_atoms pcs).
Proof.
intros. extensionality s. apply prop_ext; split; intros.
induction pcs; simpl; auto.
destruct a. destruct (expr_cmp e e0).
destruct H; apply IHpcs; auto.
destruct H; split; auto.
simpl in H. destruct H. split; auto.
induction pcs; simpl; auto.
destruct a. simpl in H. case_eq (expr_cmp e e0). intros.
split; auto. apply expr_cmp_eq in H0.
simpl; rewrite H0; auto.
rewrite H0 in H. apply IHpcs; auto.
intros. rewrite H0 in H.
simpl in H; destruct H; split; auto.
intros. rewrite H0 in H. destruct H; split; auto.
Qed.

Lemma subst_pures_delete_same : forall i e pcs B,
  list_denote pure_atom_denote (@andp state) B (subst_pures_delete i e pcs) =
  list_denote pure_atom_denote (@andp state) B (subst_pures i e pcs).
Proof.
intros. unfold subst_pures_delete.
unfold compose; rewrite <- remove_trivial_atoms_correct; auto.
Qed.

Lemma clause_denote_PureClause_sound: forall i e Gamma Delta,
  clause_denote (mkPureClause (subst_pures_delete i e Gamma) Delta) =
  clause_denote (mkPureClause (subst_pures i e Gamma) Delta).
Proof.
intros. unfold clause_denote. extensionality s.
apply prop_ext; split; simpl; intros.
rewrite subst_pures_delete_same in H; auto.
rewrite subst_pures_delete_same in H0; auto.
Qed.

Lemma clause_denote_NegSpaceClause_sound: forall i e Gamma Sigma Delta,
  clause_denote (NegSpaceClause (subst_pures_delete i e Gamma) Sigma Delta) =
  clause_denote (NegSpaceClause (subst_pures i e Gamma) Sigma Delta).
Proof.
intros. unfold clause_denote.
extensionality s; apply prop_ext; split; intros.
rewrite subst_pures_delete_same in H; auto.
rewrite subst_pures_delete_same in H0; auto.
Qed.

Lemma clause_denote_PosSpaceClause_sound: forall i e Gamma Sigma Delta,
  clause_denote (PosSpaceClause (subst_pures_delete i e Gamma) Sigma Delta) =
  clause_denote (PosSpaceClause (subst_pures i e Gamma) Sigma Delta).
Proof.
intros. unfold clause_denote.
extensionality s; apply prop_ext; split; intros.
rewrite subst_pures_delete_same in H; auto.
rewrite subst_pures_delete_same in H0; auto.
Qed.

End Subst_Sound.

