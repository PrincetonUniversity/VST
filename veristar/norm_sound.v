Load loadpath.
Require Import ZArith Coq.Lists.List Permutation.
Require Import VST.msl.Axioms veric.Coqlib2.
Require Import VST.msl.predicates_sa.
Require Import veristar.variables veristar.datatypes veristar.list_denote
               veristar.heapresolve veristar.model_type veristar.model
               veristar.superpose veristar.clauses.

Import HeapResolve.

Module Type NORM_SOUND.
Declare Module VSM: VERISTAR_MODEL.
Import VSM VeriStarLogic Superposition.

Axiom norm_sound : forall sigma sc s,
  clause_denote sc s -> setd clause_denote (@andp _) TT sigma s ->
  clause_denote (HeapResolve.norm sigma sc) s.

End NORM_SOUND.

Module Norm_Sound (VSM: VERISTAR_MODEL) : NORM_SOUND with Module VSM := VSM.
Module VSM := VSM.
Import VSM VeriStarLogic Superposition.

Import sepalg.

Lemma subst_expr_sound v e e' s :
  (Var v === e) s -> (expr_denote e' s = expr_denote (subst_expr v e e') s).
Proof with simpl in *; auto.
unfold var_eq. intro A. destruct e'... if_tac... rewrite <- H...
Qed.

Lemma join_var_eq : forall (s0 s1 s : state) x y,
  join s0 s1 s -> (x === y) s0 -> (x === y) s.
Proof.
intros.
destruct s; destruct s0; destruct s1. destruct H. simpl in *. destruct H.
unfold var_eq in *; subst; auto.
Qed.

Lemma join_var_eq' : forall (s0 s1 s : state) x y,
  join s0 s1 s -> (x === y) s -> (x === y) s0.
Proof.
intros.
destruct s; destruct s0; destruct s1. destruct H. simpl in *. destruct H.
unfold var_eq in *; subst; auto.
Qed.

Lemma subst_space_atom_sound:
   forall (v : datatypes.var) (e : expr) (s : state) (Heq : (Var v === e) s) sa,
  space_atom_denote sa s = space_atom_denote (subst_space v e sa) s.
Proof with simpl in *; auto.
destruct sa... rewrite <- subst_expr_sound...
destruct (val2loc (expr_denote e0 s))... rewrite <- subst_expr_sound...
rewrite <- subst_expr_sound... rewrite <- subst_expr_sound...
Qed.


Lemma subst_space_atoms_sound v e sigma s :
  (Var v === e) s ->
  space_denote sigma s = space_denote (map (subst_space v e) sigma) s.
Proof with simpl; auto.
intro A; revert s A; induction sigma... simpl; intros s A.
apply prop_ext. split; intro B. destruct B as [x [y [B [C D]]]].
exists x; exists y. rewrite (subst_space_atom_sound v e) in C.
split; auto. split; auto. rewrite <- IHsigma; auto.
eapply join_var_eq'; eauto. eapply join_var_eq'; eauto.
destruct B as [x [y [B [C D]]]]. exists x; exists y. split; auto.
rewrite <- subst_space_atom_sound in C; auto. split; auto.
rewrite IHsigma; auto. eapply join_var_eq'; eauto. eapply join_var_eq'; eauto.
Qed.

Lemma normalize1_3_sound pc sc s :
  clause_denote pc s -> clause_denote sc s ->
  clause_denote (normalize1_3 pc sc) s.
Proof with destruct delta; try destruct p; try destruct e; simpl; auto.
intros A B; unfold normalize1_3; destruct pc...
simpl in A. destruct sc; auto; intro C; rewrite (@listd_sort_uniq_un _ state);
try solve [apply pure_atom_cmp_eq]. rewrite listd_app, listd_unfold_un.
rewrite (@listd_sort_uniq_inter _ state) in C. 2: apply pure_atom_cmp_eq.
rewrite listd_app, listd_unfold_inter in C; destruct C as [C D].
specialize (A C). specialize (B D). rewrite (@listd_unfold_un _ state) in B.
destruct A as [A | A]; [ destruct B as [B | B]; right | left; auto].
rewrite listd_unfold_un; left... rewrite listd_unfold_un. right.
unfold space_denote in B; unfold subst_spaces.
solve[rewrite <- subst_space_atoms_sound; auto].
rewrite listd_app, listd_unfold_un.
rewrite (@listd_sort_uniq_inter _ state) in C. 2: apply pure_atom_cmp_eq.
rewrite listd_app, listd_unfold_inter in C; destruct C as [C D].
specialize (A C). destruct A as [A | A]; [ | left; auto].
rewrite listd_unfold_inter in D. destruct D as [D E].
unfold subst_spaces in E. rewrite <- subst_space_atoms_sound in E; auto.
simpl in B. rewrite (@listd_unfold_inter _ state) in B. right; apply B.
split; auto.
Qed.

Require Import Bool.

Lemma empty_state (s : state) : exists s0, emp s0 /\ join s0 s s.
Proof with auto.
generalize (join_ex_identities s); intros [s0 [A [s' B]]].
exists s0; split... assert (s = s'). apply (A _ _ B). subst s...
Qed.

Lemma lseg_nilnil sigma s :
  space_denote sigma s =
  (space_atom_denote (Lseg Nil Nil) * space_denote sigma)%pred s.
Proof with simpl; auto; try congruence.
apply prop_ext; split; intro A. destruct (empty_state s) as [s0 [B C]].
exists s0; exists s. split... split... simpl. rewrite empstate_empheap in B.
constructor... constructor...
destruct A as [x [y [A [B C]]]]. simpl in B. inversion B; subst...
cut (y = s); [ intro X; rewrite <- X; auto | ].
inversion A; subst. destruct y as [y1 y2], s as [s1 s2]; f_equal...
apply A.
Qed.

Lemma lseg_vv sigma v s :
  space_denote sigma s =
  (space_atom_denote (Lseg (Var v) (Var v)) * space_denote sigma)%pred s.
Proof with simpl; auto; try congruence.
apply prop_ext; split; intro A. destruct (empty_state s) as [s0 [B C]].
exists s0; exists s. split... split... simpl.
constructor... apply empstate_empheap...
apply var_nil_or_loc.
destruct A as [x [y [A [B C]]]]. simpl in B. inversion B; subst...
cut (y = s); [ intro X; rewrite <- X; auto | ].
inversion A; subst. destruct y as [y1 y2], s as [s1 s2]; f_equal...
apply A.
Qed.

Lemma drop_reflex_lseg_sound sigma s :
  space_denote sigma s = space_denote (drop_reflex_lseg sigma) s.
Proof with simpl; auto; try congruence.
apply prop_ext; split; intro A.
revert s A; induction sigma... intros s [x [y [A [B C]]]].
generalize A; intros [[A0 A1] A2].
destruct a; [exists x; exists y; split; auto | ].
destruct e; destruct e0. inversion B; simpl; auto; try congruence; subst. apply IHsigma.
cut (y = s); [ intro X; rewrite <- X; auto | ].
destruct y as [y1 y2], s as [s1 s2]; f_equal...
exists x; exists y; split...
exists x; exists y; split...
rewrite if_negb; remember (eq_var v v0) as b; destruct b.
2: exists x; exists y; split...
unfold eq_var in Heqb. apply eq_pos_var_eqZ in Heqb. inversion Heqb; subst.
inversion B; subst.
cut (y = s); [ intro X; rewrite <- X; auto | ].
destruct y as [y1 y2], s as [s1 s2]; f_equal... apply IHsigma...
(* <-- *)
revert s A; induction sigma... intros s A. destruct a in A |- *.
destruct A as [x [y [A [B C]]]]. exists x; exists y; split...
remember e as b1; remember  e0 as b2. destruct b1, b2 in A |- *.
rewrite <- lseg_nilnil...
destruct A as [x [y [A [B C]]]]; exists x; exists y; split...
destruct A as [x [y [A [B C]]]]; exists x; exists y; split...
rewrite if_negb in A; remember (eq_var v v0) as b; destruct b.
apply eq_pos_var_eqZ in Heqb; inversion Heqb; subst. rewrite <- lseg_vv...
destruct A as [x [y [A [B C]]]]; exists x; exists y; split...
Qed.

Lemma normalize2_4_sound sc s :
  clause_denote sc s -> clause_denote (normalize2_4 sc) s.
Proof with try solve [simpl; auto; congruence].
intro A; destruct sc... intro B. specialize (A B). clear B.
rewrite (@listd_unfold_un _ state) in A |- *. destruct A; [ left; auto | ].
right; rewrite <- drop_reflex_lseg_sound...
intro B. rewrite (@listd_unfold_inter _ state) in B. destruct B as [B C].
rewrite <- drop_reflex_lseg_sound in C. apply A.
rewrite (@listd_unfold_inter _ state); split...
Qed.

Lemma norm_sound sigma sc s :
  clause_denote sc s -> setd clause_denote (@andp _) TT sigma s ->
  clause_denote (norm sigma sc) s.
Proof with simpl; auto; try congruence.
unfold norm. intros A B. apply normalize2_4_sound. apply listd_foldr_pred...
intros x a C. apply normalize1_3_sound...
rewrite (@listd_sort_inter _ state) with (cmp := (rev_cmp compare_clause2)); auto.
Qed.

End Norm_Sound.






