Load loadpath.
Require Import ZArith Coq.Lists.List Permutation.
Require Import VST.msl.Axioms msl.Coqlib2.
Require Import VST.msl.predicates_sa.
Require Import veristar.datatypes veristar.clauses
               veristar.list_denote veristar.heapresolve
               veristar.model_type veristar.model veristar.compare.
Require Import veristar.superpose.

(* clause lemmas
   -Interpretation of clauses under reordering, etc. *)

Module Type CL_SOUND.

Declare Module VSM : VERISTAR_MODEL. Import VSM VeriStarLogic.

Axiom order_eqv_sound : forall a,
  pure_atom_denote a = pure_atom_denote (order_eqv_pure_atom a).

Axiom order_eqv_clause_sound : forall c s,
  clause_denote (order_eqv_clause c) s <-> clause_denote c s.

Axiom clause_setd_listd : forall l b s,
  listd clause_denote inter b l s ->
  setd clause_denote inter b (clause_list2set l) s.

Axiom rev_cmp_eq : forall {A:Type} (f : A -> A -> comparison) (a1 a2 : A),
  Eq = rev_cmp f a1 a2 -> rev_cmp f a1 a2 = f a1 a2.

Axiom in_sort_uniq : forall c l,
  In c (rsort_uniq (rev_cmp compare_clause) l) -> In c l.

End CL_SOUND.

Module CL_Sound (VSM : VERISTAR_MODEL) : CL_SOUND with Module VSM := VSM.
Module VSM := VSM.
Import VSM VeriStarLogic.

Import sepalg.

Lemma order_eqv_sound a :
  pure_atom_denote a = pure_atom_denote (order_eqv_pure_atom a).
Proof.
intros; destruct a; unfold pure_atom_denote in *; simpl in *.
remember (expr_cmp e e0) as b; destruct b; auto; apply var_eq_sym'.
Qed.

Lemma list_denote_intersection_filter_nonreflex (B: spred) (l: list pure_atom) :
  listd pure_atom_denote inter B l =
  listd pure_atom_denote inter B (filter nonreflex_atom l).
Proof with simpl; auto.
intros; induction l... rewrite IHl; clear IHl.
remember (nonreflex_atom a) as b; destruct b...
destruct a; simpl in *.
assert (expr_cmp e e0 = Eq).
  remember (expr_cmp e e0) as b; destruct b; try reflexivity.
  inversion Heqb. inversion Heqb. clear Heqb.
symmetry in H; apply comp_eq in H; auto. rewrite H.
extensionality s; apply prop_ext; split; simpl; auto.
intros [H1 H2]; auto. split; auto. apply var_eq_refl.
Qed.

Lemma list_denote_normalize_pure_atoms :
  forall Q (B:spred) (l:list pure_atom)
     (Qassoc: forall x y z , Q x (Q y z) = Q (Q x y) z)
     (Qsymm: forall x y, Q x y = Q y x)
     (Hcmp: forall x y, Eq = pure_atom_cmp x y ->
       (forall P, Q (pure_atom_denote x) (Q (pure_atom_denote y) P) =
                  Q (pure_atom_denote y) P)),
  list_denote pure_atom_denote Q B l =
  list_denote pure_atom_denote Q B (normalize_atoms l).
Proof with simpl; auto.
intros; unfold normalize_atoms; rewrite listd_sort_uniq...
induction l... rewrite <-order_eqv_sound, <-IHl...
Qed.

Lemma list_denote_intersection_normalize_pure_atoms B l :
  list_denote pure_atom_denote inter B l =
  list_denote pure_atom_denote inter B (normalize_atoms l).
Proof.
intros; apply list_denote_normalize_pure_atoms.
intros. rewrite andp_assoc; trivial.
intros. rewrite andp_comm; trivial.
intros. rewrite <- pure_atom_cmp_eq in H. rewrite H.
rewrite interA. extensionality s; apply prop_ext.
split; intros H1. destruct H1 as [[H1 H2] H3]; split; auto.
destruct H1; split; auto. split; auto.
Qed.

Lemma list_denote_union_normalize_pure_atoms B l :
  list_denote pure_atom_denote un B l =
  list_denote pure_atom_denote un B (normalize_atoms l).
Proof.
intros.
apply list_denote_normalize_pure_atoms.
intros. rewrite union_assoc; trivial.
intros. rewrite union_com; trivial.
intros. rewrite <- pure_atom_cmp_eq in H. rewrite H.
rewrite <- union_assoc.
extensionality s; apply prop_ext; split; intros.
inversion H0. inversion H1; left; auto.
right; auto. inversion H0. left; left; auto. right; auto.
Qed.

Lemma list_denote_normalize_filter_nonreflex_atom B l :
  list_denote pure_atom_denote inter B
      (normalize_atoms (filter nonreflex_atom l)) =
  list_denote pure_atom_denote inter B l.
Proof.
intros; rewrite <- list_denote_intersection_normalize_pure_atoms.
rewrite <- list_denote_intersection_filter_nonreflex; auto.
Qed.

Lemma order_eqv_clause_sound c s :
  clause_denote (order_eqv_clause c) s <-> clause_denote c s.
Proof.
intros. destruct c; simpl;
  rewrite list_denote_normalize_filter_nonreflex_atom;
    rewrite <- list_denote_union_normalize_pure_atoms;
      apply iff_refl.
Qed.

(* todo: make the following lems more general *)

Lemma clause_setd_listd l b s :
  listd clause_denote inter b l s ->
  setd clause_denote inter b (clause_list2set l) s.
Proof with simpl; auto; try solve[congruence].
intro H1. apply setd_fold_left...
intros c cls s0 H2 H3. apply setd_add...
unfold setd; rewrite empty_set_elems...
rewrite (@listd_unfold_inter clause state) in H1.
destruct H1; auto.
Qed.

Lemma rev_cmp_eq {A:Type} (f : A -> A -> comparison) (a1 a2 : A) :
  Eq = rev_cmp f a1 a2 -> rev_cmp f a1 a2 = f a1 a2.
Proof with auto; try congruence.
unfold rev_cmp; destruct (f a1 a2)...
Qed.

Lemma in_insert_uniq c c' l :
  In c (insert_uniq (rev_cmp compare_clause) c' l) ->
  c' = c \/ In c l.
Proof with simpl; auto; try solve[congruence].
induction l...
remember (rev_cmp compare_clause c' a) as b; destruct b...
inversion 1; subst... cut (c' = c \/ In c l)... inversion 1...
Qed.

Lemma compare_clause_refl d : Eq = rev_cmp compare_clause d d.
Proof with simpl; auto.
unfold rev_cmp. rewrite comp_refl; auto.
Qed.

Lemma in_sort_uniq c l :
  In c (rsort_uniq (rev_cmp compare_clause) l) -> In c l.
Proof with simpl; auto; try solve[congruence].
induction l... intro H1.
generalize compare_clause_refl as H2; intros.
remember (rev_cmp compare_clause a c) as b; destruct b.
generalize Heqb; apply rev_cmp_eq in Heqb; rewrite Heqb.  intro Hx; apply comp_eq in Hx; auto.
right; apply IHl. generalize (in_insert_uniq _ _ _ H1) as H3.
inversion 1; subst...
right; apply IHl. generalize (in_insert_uniq _ _ _ H1) as H3.
inversion 1; subst...
Qed.

End CL_Sound.

(* some general lemmas about positives: not sure where to put these so they go
   here for now *)

Lemma positive_base_case: forall n, 0 = nat_of_P n - 1 -> n=1%positive.
Proof. intros. generalize (lt_O_nat_of_P n); intro.
 assert (nat_of_P n = 1) by omega.
 assert (nat_of_P 1%positive = 1) by reflexivity.
 rewrite <- H2 in H1.
 generalize (nat_of_P_inj n 1 H1); intro; subst n; auto.
Qed.



