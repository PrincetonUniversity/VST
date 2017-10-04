Load loadpath.
Require Import ZArith Coq.Lists.List Permutation.
Require Import VST.msl.Axioms.
Require Import VST.msl.predicates_sa.
Require Import VST.veric.Coqlib2.
Require Import veristar.variables veristar.datatypes veristar.clauses
               veristar.list_denote veristar.model_type veristar.model
               veristar.basic veristar.compare.

Module Type SPRED_LEMMAS.
Declare Module VSM : VERISTAR_MODEL.
Import VSM VeriStarLogic.

End SPRED_LEMMAS.

Module SPredLemmas (VSM : VERISTAR_MODEL) <: SPRED_LEMMAS
  with Module VSM := VSM.
Module VSM := VSM.
Import VSM VeriStarLogic.

Import sepalg.

(* properties of spred operators *)

Module spred. Section spred.
Variables x y z : spred.

Local Open Scope pred.

Lemma andpN : x && TT = x.
Proof. apply andp_TT. Qed.

Lemma andpS : x && y = y && x.
Proof. apply andp_comm. Qed.

Lemma andpA : x && (y && z) = (x && y) && z.
Proof. rewrite andp_assoc; auto. Qed.

Lemma orpN : x || FF = x.
Proof.
extensionality; apply prop_ext; split; [solve[intros [H|H]; [auto|case H]; auto]
|solve[left; auto]].
Qed.

Lemma orpS : x || y = y || x.
Proof. apply union_com. Qed.

Lemma orpA : x || (y || z) = (x || y) || z.
Proof. rewrite union_assoc; auto. Qed.

Lemma sepconS : sepcon x y = sepcon y x.
Proof. apply sepcon_comm. Qed.

Lemma sepconA : x * (y * z) = (x * y) * z.
Proof. rewrite sepcon_assoc; auto. Qed.

End spred. End spred.

Lemma emp_sep_emp h h1 h2 : join h h1 h2 -> emp h -> emp h1 -> emp h2.
Proof. intros; rewrite <-(emp_sepcon emp); exists h; exists h1; split; auto. Qed.

Lemma space_denote_permute l l' :
  Permutation l l' -> space_denote l = space_denote l'.
Proof.
intros;
apply (listd_perm space_atom_denote _ emp spred.sepconS spred.sepconA l l' H).
Qed.

Lemma space_insert sa l :
  space_denote (insert (rev_cmp compare_space_atom) sa l) =
  space_denote (sa :: l).
Proof.
intros; eapply listd_perm;
[apply spred.sepconS|apply spred.sepconA|apply perm_insert].
Qed.

Lemma eq_space_atomlist_sound (al bl : list space_atom) :
  true = eq_space_atomlist al bl ->
  space_denote al = space_denote bl.
Proof.
intros H; unfold eq_space_atomlist, isEq in H.
remember (compare_list compare_space_atom al bl) as j; destruct j; inversion H.
solve[apply comp_eq in Heqj; subst; auto].
Qed.

Lemma expr_eq_eq' : forall e1 e2, true = expr_eq e1 e2 -> e1=e2.
Proof.
unfold expr_eq; intros; do_comp expr_cspec e1 e2; subst; auto; congruence.
Qed.

Lemma pure_atom_denote_order_eqv_pure_atom : forall a,
  pure_atom_denote a = pure_atom_denote (order_eqv_pure_atom a).
Proof.
intros; destruct a; unfold pure_atom_denote in *; simpl in *.
remember (expr_cmp e e0) as b; destruct b; try reflexivity.
solve[apply var_eq_sym'].
Qed.

Lemma list_denote_normalize_pure_atoms:
 forall Q (B:spred) (l:list pure_atom)
     (Qassoc: forall x y z , Q x (Q y z) = Q (Q x y) z)
     (Qsymm: forall x y, Q x y = Q y x)
     (Hcmp: forall x y, Eq = pure_atom_cmp x y ->
                        (forall P, Q (pure_atom_denote x) (Q (pure_atom_denote y) P) = Q (pure_atom_denote y) P)),
list_denote pure_atom_denote Q B l =
list_denote pure_atom_denote Q B (normalize_atoms l).
Proof.
intros.
unfold normalize_atoms.
  rewrite listd_sort_uniq.
    rewrite listd_map.
      reflexivity.
      intros. rewrite <- pure_atom_denote_order_eqv_pure_atom. trivial.
      apply Qsymm.
      apply Qassoc.
    apply Hcmp.
Qed.

Lemma union_contractive:
forall {A} x, (@orp A) x x = x.
Proof.
intros. unfold orp.
extensionality a. apply prop_ext. split; intros.
 destruct H; assumption. left; assumption.
Qed.

Lemma list_denote_union_normalize_pure_atoms:
 forall(B:spred) (l:list pure_atom),
list_denote pure_atom_denote (@orp state) B l =
list_denote pure_atom_denote (@orp state) B (normalize_atoms l).
Proof.
intros.
apply list_denote_normalize_pure_atoms.
  intros. rewrite union_assoc; trivial.
  intros. rewrite union_com; trivial.
  intros. rewrite <- pure_atom_cmp_eq in H. rewrite H.
      rewrite <- union_assoc.
      rewrite union_contractive. reflexivity.
Qed.

Lemma intersection_contractive:
forall {A} x, (@andp A) x x = x.
Proof.
intros. unfold andp.
extensionality a. apply prop_ext. split; intros. destruct H; assumption. split; assumption.
Qed.

Lemma list_denote_intersection_normalize_pure_atoms:
 forall(B:spred) (l:list pure_atom),
list_denote pure_atom_denote (@andp state) B l =
list_denote pure_atom_denote (@andp state) B (normalize_atoms l).
Proof.
intros.
apply list_denote_normalize_pure_atoms.
  intros. rewrite andp_assoc; trivial.
  intros. rewrite andp_comm; trivial.
  intros.
  rewrite <- pure_atom_cmp_eq in H. rewrite H.
      rewrite <- andp_assoc.
      rewrite intersection_contractive. reflexivity.
Qed.

Lemma expr_cmp_eq: forall e e',
  expr_cmp e e' = Eq -> (e === e') = TT.
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
  expr_cmp e e' = Eq -> (e === e') s.
Proof.
intros.
rewrite (expr_cmp_eq _ _ H). trivial.
Qed.

Lemma list_denote_intersection_filter_nonreflex:
 forall(B:spred) (l:list pure_atom),
list_denote pure_atom_denote (@andp state) B l =
list_denote pure_atom_denote (@andp state) B (filter nonreflex_atom l).
Proof.
intros.
induction l; simpl. reflexivity.
rewrite IHl. clear IHl.
remember (nonreflex_atom a) as b; destruct b; simpl.
  reflexivity.
destruct a; simpl in *.
  assert (expr_cmp e e0 = Eq).
    remember (expr_cmp e e0) as b; destruct b; try reflexivity.
    inversion Heqb. inversion Heqb.
  clear Heqb.
rewrite (expr_cmp_eq _ _ H). rewrite TT_and. reflexivity.
Qed.

Lemma list_denote_normalize_filter_nonreflex_atom:
forall B l,
list_denote pure_atom_denote (@andp state) B
            (normalize_atoms (filter nonreflex_atom l))
= list_denote pure_atom_denote (@andp state) B l.
Proof.
intros.
rewrite <- list_denote_intersection_normalize_pure_atoms.
rewrite <- list_denote_intersection_filter_nonreflex; reflexivity.
Qed.

Lemma list_denote_inter_app : forall {A} (f: A -> spred) cs1 cs2 s,
  list_denote f (@andp state) TT (cs1 ++ cs2) s ->
  (list_denote f (@andp state) TT cs1 s /\
   list_denote f (@andp state) TT cs2 s).
Proof.
intros A f.
induction cs1; simpl; intros.
  split. trivial. assumption.
destruct H as [H1 H2].
 destruct (IHcs1 _ _ H2) as [H3 H4].
 split. split; assumption. assumption.
Qed.

Lemma list_denote_assoc_sym_id : forall {A T} (E: A -> T) Q B C l
  (CID : forall x, Q x C = x)
  (QSYM : forall x y, Q x y = Q y x)
  (QASSOC : forall x y z, Q x (Q y z) = Q (Q x y) z),
  list_denote E Q B l = Q B (list_denote E Q C l).
Proof.
intros.
induction l; simpl; intros; auto.
rewrite IHl. rewrite QSYM. rewrite <- QASSOC.
pattern (Q (list_denote E Q C l) (E a)).
rewrite QSYM. auto.
Qed.

Lemma list_denote_union_left : forall {A} (f: A -> spred) cs1 cs2 s,
  list_denote f (@orp state) FF cs1 s ->
  list_denote f (@orp state) FF (cs1 ++ cs2) s.
Proof.
intros.
rewrite listd_app.
rewrite (@listd_unfold_un _ state).
left. assumption.
Qed.

Lemma list_denote_union_right : forall {A} (f: A -> spred) cs1 cs2 s,
  list_denote f (@orp state) FF cs2 s ->
  list_denote f (@orp state) FF (cs1 ++ cs2) s.
Proof.
intros.
rewrite listd_app.
rewrite (@listd_unfold_un _ state).
right. assumption.
Qed.

Lemma list_denote_sepcon_sort :
  forall {A} (E:A -> spred) (B:spred) (l:list A) cmp s,
    list_denote E sepcon B l s <->
    list_denote E sepcon B (rsort cmp l) s.
Proof.
intros.
rewrite (listd_sort). split; trivial.
intros; rewrite sepcon_comm; auto.
intros; rewrite sepcon_assoc; auto.
Qed.

Lemma empty_not_singleton: forall c, M.empty <> M.singleton c.
 Proof. intros. intro.
   contradiction (@M.empty_spec c).
   rewrite H. rewrite M.singleton_spec. auto.
Qed.

Lemma singleton_inv:
  forall x y, M.singleton x = M.singleton y -> x=y.
Proof.
intros.
apply (M.singleton_spec y).
rewrite <- H. apply M.singleton_spec. auto.
Qed.

Lemma elements_singleton: forall c, M.elements (M.singleton c) = [c].
Proof.
intros.
assert (X:= M.singleton_spec c).
assert (ND := M.elements_spec2w (M.singleton c)).
inversion ND; clear ND.
  apply False_ind.
  remember (M.elements (M.singleton c)) as l.
  destruct l.
    apply eq_sym in Heql.
    apply empty_set_elems' in Heql.
    unfold M.Empty in Heql. apply (Heql c). apply X. trivial.
  inversion H0.
assert (x = c).
  apply X. rewrite <- elements_In. rewrite <- H. left. trivial.
subst.
destruct l. trivial.
assert (c0 = c).
  apply X. rewrite <- elements_In. rewrite <- H. right. left. trivial.
subst. exfalso. apply H0. left. trivial.
Qed.

Lemma var_eq_Next: forall e e' g g' s, (e === e') s -> (g === g') s ->
space_atom_denote (Next e g) s = space_atom_denote (Next e' g') s.
Proof.
intros; simpl.
apply prop_ext; split; intros.
  rewrite H in H1. rewrite H0 in H1. assumption.
  rewrite H. rewrite H0. assumption.
Qed.

Lemma var_eq_Lseg1: forall e e' g s, (e === e') s ->
space_atom_denote (Lseg e g) s = space_atom_denote (Lseg e' g) s.
Proof.
intros; simpl.
rewrite H; auto.
Qed.

Lemma var_eq_Lseg2: forall g e e' s, (e === e') s ->
space_atom_denote (Lseg g e) s = space_atom_denote (Lseg g e') s.
Proof.
intros; simpl.
rewrite H; auto.
Qed.

Lemma var_eq_Lseg: forall e e' g g' s, (e === e') s -> (g === g') s ->
space_atom_denote (Lseg e g) s = space_atom_denote (Lseg e' g') s.
Proof.
intros.
eapply eq_trans. apply var_eq_Lseg2. apply H0.
apply var_eq_Lseg1. apply H.
Qed.

Lemma join_stacks_eq : forall s0 s1 s : state,
  join s0 s1 s -> stk s0=stk s1 /\ stk s0=stk s.
Proof.
intros.
destruct H. destruct H.
subst; split; auto.
transitivity (stk s1); auto.
Qed.

Lemma expr_denote_join: forall e s r t,
join s r t -> expr_denote e t = expr_denote e s.
Proof.
intros.
destruct e; simpl in H; simpl; intros. trivial.
destruct (join_stacks_eq _ _ _ H) as [_ D].
rewrite <- D. trivial.
Qed.

Lemma expr_denote_eq_dec_loc:
   forall x y s,
        nil_or_loc (expr_denote x s) ->
        Decidable.decidable (expr_denote x s = expr_denote y s).
Proof.
intros.
destruct H.
rewrite H.
destruct (nil_dec (expr_denote y s)); [left | right]; auto.
destruct H as [l ?].
case_eq (val2loc (expr_denote y s)); intros.
destruct (loc_eq_dec l l0).
left; subst.
eapply val2loc_inj; eauto.
right.
contradict H1. rewrite H1 in *. congruence.
right.
intro.
rewrite H1 in *; congruence.
Qed.

Lemma expr_denote_heap_ind : forall x s h h',
  expr_denote x (State s h)=expr_denote x (State s h').
Proof.
intros. destruct x; auto.
Qed.

Lemma state_join_var_eq : forall (s0 s1 s : state) x y,
  join s0 s1 s ->
  (x === y) s0 ->
  (x === y) s.
Proof.
intros.
destruct s; destruct s0; destruct s1. destruct H. simpl in *. destruct H.
unfold var_eq in *; subst; auto.
Qed.

Lemma state_join_var_eq' : forall (s0 s1 s : state) x y,
  join s0 s1 s ->
  (x === y) s ->
  (x === y) s0.
Proof.
intros.
destruct s; destruct s0; destruct s1. destruct H. simpl in *. destruct H.
unfold var_eq in *; subst; auto.
Qed.

Lemma unXX {A:Type} (P: pred A) b : un P (un P b) = un P b.
Proof.
extensionality a; apply prop_ext; split; firstorder.
Qed.

Lemma lseg_appN: forall x y s r t,
 lseg x y s -> lseg y nil_val r -> join s r t -> lseg x nil_val t.
Proof.
intros.
revert r H0 t H1; induction H; intros.
apply join_unit1_e in H2; auto. subst; auto.
specialize (IHlseg _ H4).
destruct (join_assoc H3 H5) as [hf [? ?]].
specialize (IHlseg _ H6).
econstructor 2; eauto.
intro; subst. rewrite nil_not_loc in H0; inversion H0.
Qed.

Lemma pure_atom_denote_heap_ind: forall a s h h',
pure_atom_denote a (State s h) = pure_atom_denote a (State s h').
Proof.
intros.
destruct a; simpl.
unfold var_eq. simpl.
rewrite (expr_denote_heap_ind e s h h').
rewrite (expr_denote_heap_ind e0 s h h').
reflexivity.
Qed.

Lemma pure_atoms_denote_intersection_heap_ind: forall Delta s h h',
list_denote pure_atom_denote (@andp state) TT Delta (State s h) =
list_denote pure_atom_denote (@andp state) TT Delta (State s h').
Proof.
intros Delta.
induction Delta; simpl; intros.
  reflexivity.
apply prop_ext.
split; intros; destruct H.
  split. rewrite <- (pure_atom_denote_heap_ind a s h h'). assumption.
  rewrite <- (IHDelta s h h'). assumption.
split. rewrite (pure_atom_denote_heap_ind a s h h'). assumption.
  rewrite (IHDelta s h h'). assumption.
Qed.

Lemma pure_atoms_denote_union_heap_ind: forall Delta s h h',
list_denote pure_atom_denote (@orp state) FF Delta (State s h) =
list_denote pure_atom_denote (@orp state) FF Delta (State s h').
Proof.
intros Delta.
induction Delta; simpl; intros.
  reflexivity.
apply prop_ext.
split; intros; destruct H.
  left. rewrite <- (pure_atom_denote_heap_ind a s h h'). assumption.
  right. rewrite <- (IHDelta s h h'). assumption.
left. rewrite (pure_atom_denote_heap_ind a s h h'). assumption.
  right. rewrite (IHDelta s h h'). assumption.
Qed.

Lemma lseg_nil_or_loc:
  forall x y h, lseg x y h -> nil_or_loc y.
Proof.
induction 1; auto.
Qed.

Lemma lseg_end: forall x y h,
  lseg x y h -> (x = y /\ emp h) \/ y = nil_val \/
     (exists l, val2loc y = Some l /\ emp_at l h).
Proof.
induction 1; intros; auto.
right.
destruct IHlseg as [[? ?] | [?|[l [? ?]]]]; auto.
subst.
apply join_unit2_e in H3; auto. subst h0.
apply lseg_nil_or_loc in H2.
clear H5.
destruct H2; auto; right.
destruct H2 as [l ?]; exists l.
split; auto.
apply (rawnext_out H1 H2).
contradict H.
subst l.
apply val2loc_inj with x'; auto.
right; exists l.
split; auto.
apply emp_at_join with l in H3.
apply H3. split; auto.
assert (l<>x') by (contradict H; subst; eapply val2loc_inj; eauto).
eapply rawnext_out; eauto.
Qed.

Lemma lseg_lseg_app: forall x y z h1 h2 h tz,
  lseg x y h1 ->
  lseg y z h2 ->
  join h2 h1 h ->
 val2loc z = Some tz ->
  emp_at tz h ->
  lseg x z h.
Proof.
intros.
revert z h2 H0 h H1 tz H2 H3; induction H; intros.
apply join_unit2_e in H2; auto; subst; auto.
specialize (IHlseg _ _ H4).
destruct (join_assoc H3 (join_comm H5)) as [hf [? ?]].
specialize (IHlseg _ (@join_comm _ _ Perm_heap _ _ _ H8) _ H6).
assert (emp_at tz hf). apply emp_at_join with tz in H9. apply H9 in H7. destruct H7; auto.
specialize (IHlseg H10).
eapply lseg_cons; eauto.
intro; subst z0.
assert (x'=tz) by congruence. subst x'.
clear H6.
apply emp_at_join with tz in H9.
apply H9 in H7. destruct H7.
clear - H1 H6. eapply rawnext_not_emp; eauto.
eapply rawnext2rawnext'; eauto.
Qed.

Lemma Space_denote_cons: forall a L,
space_denote (a::L) = sepcon (space_atom_denote a) (space_denote L).
Proof.
intros.
apply listd_cons.
Qed.

Lemma Space_denote_app: forall M L,
space_denote (M ++ L) = sepcon (space_denote M) (space_denote L).
Proof.
intros M.
induction M; simpl.
  intros. rewrite (emp_sepcon (space_denote L)). trivial.
intros.
  rewrite (IHM L). rewrite sepconA; auto with typeclass_instances.
Qed.

Lemma Space_denote_rev: forall L,
space_denote (rev L) = (space_denote L).
Proof.
intros.
apply space_denote_permute. apply Permutation_sym.  apply Permutation_rev.
Qed.

End SPredLemmas.
