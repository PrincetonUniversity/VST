Load loadpath.
Require Import ZArith Coq.Lists.List Permutation.
Require Import VST.msl.Axioms VST.veric.Coqlib2.
Require Import VST.msl.predicates_sa.
Require Import veristar.datatypes veristar.clauses veristar.clause_lemmas
               veristar.cclosure veristar.list_denote veristar.superpose_modelsat
               veristar.basic veristar.compare.
Import Superposition.
Require Import veristar.model_type veristar.model.

Module Type SP_SOUND.
Declare Module VSM : VERISTAR_MODEL.
Import VSM VeriStarLogic.

Axiom check_clauseset_Valid_sound: forall init units g u,
  check_clauseset init = (Valid, units, g, u) ->
  setd clause_denote inter TT init |-- clause_denote empty_clause.

Axiom check_clauseset_Cexample_sound: forall init units final empty R selected,
  check_clauseset init = (C_example R selected, units, final, empty) ->
  setd clause_denote inter TT init |--
    setd clause_denote inter TT selected &&
    setd clause_denote inter TT final &&
    listd clause_denote inter TT units.

(* no other convenient place to expose these facts *)

Axiom simplify_sound : forall l c s,
  listd clause_denote inter TT l s -> clause_denote c s ->
  clause_denote (simplify l c) s.

Axiom simplify_atoms_sound : forall l sigma s,
  listd clause_denote inter TT l s -> space_denote sigma s ->
  space_denote (simplify_atoms l sigma) s.

End SP_SOUND.

Module SP_Sound (VSM : VERISTAR_MODEL) : SP_SOUND with Module VSM := VSM.
Module VSM := VSM.
Import VSM VeriStarLogic.

Module CCS := CCSound VSM. Import CCS.

Implicit Arguments list_denote [A T].
Local Notation "'listd'" := list_denote.

Implicit Arguments andp [A].
Local Notation "'inter'" := (@andp _). (*implicit arguments acting weird*)

(* the following five rules (barring reflexivity resolution, which is performed
   during the simplification phase) are collected in rule "sp" *)

Require Import Bool.

Definition reflexivity_resolution (d : clause) l0 : list clause :=
  match d with
  | PureClause (Eqv u v :: neg) pos _ _ =>
    if expr_eq u v then mkPureClause neg pos :: l0 else l0
  | _ => l0
  end.

Definition ordered_factoring (c : clause) l0 : list clause :=
  match c with
  | PureClause nil (Eqv s t :: Eqv u v :: pos) _ _ =>
    if pure_atom_eq (Eqv s t) (Eqv u v)
    then mkPureClause nil (insert_uniq pure_atom_cmp
              (norm_pure_atom (Eqv s t)) pos)
                     :: l0
    else l0
  | _ => l0
  end.

Definition positive_superposition (c d : clause) l0 : list clause :=
  match c, d with
  (* positive (right) superposition *)
  | PureClause neg (Eqv (Var s0 as s) t :: pos) _ _,
           PureClause neg' (Eqv (Var s'0 as s') v :: pos') _ _ =>
    if expr_eq s s' && expr_lt t s && expr_lt v s' &&
       pure_atom_gt1 (Eqv s t) pos && pure_atom_gt1 (Eqv s' v) pos' &&
       pure_atom_gt (Eqv s t) (Eqv s' v) &&
       greater_than_all s0 neg && greater_than_all s'0 neg'
    then mkPureClause
      (merge pure_atom_cmp neg neg')
      (insu_atm (norm_pure_atom (Eqv t v)) (merge pure_atom_cmp pos pos')) :: l0
    else l0
  | _, _ => l0
  end.

Definition negative_superposition (c d : clause) l0 : list clause :=
  match c, d with
  (* negative (left) superposition *)
  | PureClause (Eqv s' v :: neg') pos' _ _,
        PureClause neg (Eqv (Var s0 as s) t :: pos) _ _ =>
    if expr_eq s s' && expr_lt t s && expr_lt v s' &&
       pure_atom_gt1 (Eqv s t) pos && greater_than_all s0 neg
    then mkPureClause
      (insu_atm (norm_pure_atom (Eqv t v)) (merge pure_atom_cmp neg neg'))
      (merge pure_atom_cmp pos pos') :: l0
    else l0
  | _, _ => l0
  end.

Lemma positive_superposition_sound c d l0 s :
  clause_denote c s -> clause_denote d s -> listd clause_denote inter TT l0 s ->
  listd clause_denote inter TT (positive_superposition c d l0) s.
Proof with simpl; auto.
intros A B; destruct c as [gamma delta| |]; destruct d as [gamma' delta'| |]...
2: simpl; destruct gamma, delta... 2: destruct p... 2: destruct e...
2: destruct p0... 2: destruct e...
2: simpl; destruct gamma, delta... 2: destruct p... 2: destruct e...
2: destruct p0... 2: destruct e...
destruct delta... destruct p... destruct e...
destruct delta'... destruct p... destruct e...
remember (expr_eq (Var v) (Var v0)) as b; destruct b... if_tac...
rewrite <-(expr_eq_eq' _ _ Heqb) in *. intros H. split... intros H1.
simpl in A, B. apply listd_merge_inter' in H1. destruct H1 as [H2 H3].
2: intros; rewrite pure_atom_cmp_eq...
specialize (A H2); specialize (B H3); rewrite (@listd_insert_uniq_un _ state).
2: intros x y; rewrite <-pure_atom_cmp_eq... destruct A, B.
assert (C: (e0 === e1) s) by (eapply var_eq_trans; apply var_eq_sym in H0; eauto).
left. if_tac... apply var_eq_sym...
right; apply listd_merge_un2... solve[apply pure_atom_cmp_eq; auto].
right; apply listd_merge_un1... solve[apply pure_atom_cmp_eq; auto].
right; apply listd_merge_un1... solve[apply pure_atom_cmp_eq; auto].
Qed.

Lemma negative_superposition_sound c d l0 s :
  clause_denote c s -> clause_denote d s -> listd clause_denote inter TT l0 s ->
  listd clause_denote inter TT (negative_superposition c d l0) s.
Proof with simpl; auto.
intros A B; destruct c as [gamma delta| |]; destruct d as [gamma' delta'| |]...
2: simpl; destruct gamma, delta... 2: destruct p... 2: destruct p...
2: simpl; destruct gamma, delta... 2: destruct p... 2: destruct p...
destruct gamma... destruct p... destruct delta'... destruct p...
destruct e1... remember (expr_eq (Var v) e) as b; destruct b...
if_tac; [simpl|simpl; auto]; rewrite interS; simpl. intro H3. split...
rewrite (@listd_insert_uniq_inter _ state)... 2: apply pure_atom_cmp_eq.
intros [H1 H2].
assert ((e2 === e0) s). if_tac in H1; simpl in H1... apply var_eq_sym...
apply listd_merge_inter' in H2. destruct H2 as [H4 H5]. simpl in B; spec B...
2: intros x y; rewrite <-pure_atom_cmp_eq...
destruct B.
assert ((e === e0) s). apply var_eq_trans with (y:=e2)...
solve[apply expr_eq_eq' in Heqb; rewrite Heqb in H0; auto].
simpl in A; spec A... split...
apply listd_merge_un2... solve[apply pure_atom_cmp_eq].
apply listd_merge_un1... solve[apply pure_atom_cmp_eq].
Qed.

Lemma reflexivity_resolution_sound c l0 s :
  clause_denote c s -> listd clause_denote inter TT l0 s ->
  listd clause_denote inter TT (reflexivity_resolution c l0) s.
Proof with
try solve [simpl; destruct delta as [|p]; simpl; auto; destruct p; simpl; auto].
intros A; destruct c as [gamma delta| |]...
simpl; destruct gamma as [|p]; simpl; auto; destruct p...
remember (expr_eq e e0) as b; destruct b; simpl; try split; auto.
intro Hyp; apply A; rewrite (expr_eq_eq' _ _ Heqb); simpl; split; auto.
solve[apply var_eq_refl].
Qed.

Lemma ordered_factoring_sound c l0 s :
  clause_denote c s -> listd clause_denote inter TT l0 s ->
  listd clause_denote inter TT (ordered_factoring c l0) s.
Proof with
simpl; auto;
try solve [simpl; destruct delta as [|p]; simpl; auto; destruct p; simpl; auto].
intros A; destruct c as [gamma delta| |]...
destruct gamma... destruct delta... destruct p... destruct delta... destruct p...
(*simpl; destruct delta as [|p]; simpl; auto; destruct p...
destruct delta as [|p]; simpl; auto; destruct p...*)
remember (expr_eq e e1) as b1; remember (expr_eq e0 e2) as b2.
destruct b1, b2...
if_tac... simpl; split; auto. intro Hyp.
rewrite (listd_insert_uniq_un pure_atom_denote FF). 2: apply pure_atom_cmp_eq.
rewrite (expr_eq_eq' _ _ Heqb1), (expr_eq_eq' _ _ Heqb2) in A |- *.
simpl in A; destruct A as [A|[A|A]]; [auto| | |right; auto].
solve [left; if_tac; simpl; solve[auto | apply var_eq_sym; auto]].
solve [left; if_tac; simpl; solve[auto | apply var_eq_sym; auto]].
replace (pure_atom_eq (Eqv e e0) (Eqv e1 e2)) with false; auto.
unfold pure_atom_eq; simpl.
unfold expr_eq in Heqb1. destruct (expr_cmp e e1); simpl; try congruence.
unfold expr_eq in Heqb2. destruct (expr_cmp e0 e2);simpl; try congruence.
replace (pure_atom_eq (Eqv e e0) (Eqv e1 e2)) with false; auto.
unfold pure_atom_eq; simpl.
unfold expr_eq in Heqb1. destruct (expr_cmp e e1); simpl; try congruence.
replace (pure_atom_eq (Eqv e e0) (Eqv e1 e2) ) with false; auto.
unfold pure_atom_eq; simpl.
unfold expr_eq in Heqb1. destruct (expr_cmp e e1); simpl; try congruence.
Qed.

Lemma sp_sound ce c d l0 s :
  clause_denote c s -> clause_denote d s -> listd clause_denote inter TT l0 s ->
  listd clause_denote inter TT (sp ce c d l0) s.
Proof with simpl; auto.
intros H1 H2 H3.
generalize (negative_superposition_sound c d l0 s) as H4; intro.
generalize (positive_superposition_sound c d l0 s) as H5; intro.
specialize (H4 H1 H2 H3); specialize (H5 H1 H2 H3).
rewrite (@listd_unfold_inter _ state). split...
unfold sp. destruct ce...
Qed.

Lemma ef_aux_sound neg u0 u v pos0 pos l0 s :
  (listd pure_atom_denote inter TT neg s ->
    listd pure_atom_denote un FF
        (merge pure_atom_cmp (List.rev pos0) (Eqv (Var u0) v :: pos)) s) ->
  list_denote clause_denote inter TT l0 s ->
  (Var u0 === u) s ->
  listd clause_denote inter TT (ef_aux neg u0 u v pos0 pos l0) s.
Proof with auto.
intros H1 H2 (*H3*) H4. revert pos0 H1 H2. induction pos... simpl. destruct a...
remember (expr_eq e u) as b; destruct b... intros pos0 H1 H2. if_tac...
rewrite (@listd_unfold_inter _ state). split...
assert (H5 :
      listd pure_atom_denote inter TT (Eqv v e0 :: neg) s ->
      listd pure_atom_denote un FF
        (merge pure_atom_cmp (List.rev pos0) (Eqv u e0 :: pos)) s).
  simpl. intros [H5 H6]. specialize (H1 H6). apply expr_eq_eq' in Heqb. subst.
  apply listd_merge_un' in H1. destruct H1.
  apply listd_merge_un1. apply pure_atom_cmp_eq. auto.
  apply listd_merge_un2. apply pure_atom_cmp_eq. auto.
  simpl in H. destruct H.
  left. apply var_eq_trans with (y:= v)... apply var_eq_trans with (y:=Var u0)...
    apply var_eq_sym...
  destruct H. left... right...
intros; rewrite pure_atom_cmp_eq; auto.
simpl; split...
simpl. rewrite (@listd_insert_uniq_inter _ state). intros [H6 H7].
2: apply pure_atom_cmp_eq.
rewrite (@listd_insert_uniq_un _ state). 2: apply pure_atom_cmp_eq.
spec H5. simpl; split... if_tac in H6... apply var_eq_sym...
apply listd_merge_un' in H5. destruct H5 as [H5|H5].
  right. apply listd_merge_un1. apply pure_atom_cmp_eq. auto.
simpl in H5; destruct H5 as [H|H]. left. if_tac... apply var_eq_sym...
right. apply listd_merge_un2. apply pure_atom_cmp_eq. simpl. right...
apply expr_eq_eq' in Heqb; subst.
intros; rewrite pure_atom_cmp_eq; auto.
apply IHpos. intros H6. specialize (H1 H6).
apply listd_merge_un' in H1. destruct H1.
apply listd_merge_un1. apply pure_atom_cmp_eq.
rewrite (@listd_un_rev _ state), (@listd_insert_uniq_un _ state).
2: apply pure_atom_cmp_eq.
rewrite (@listd_un_rev _ state) in H. solve[right; apply H].
simpl in H; destruct H.
apply listd_merge_un2. apply pure_atom_cmp_eq. simpl; left...
destruct H.
apply listd_merge_un1. apply pure_atom_cmp_eq.
rewrite (@listd_un_rev _ state), (@listd_insert_uniq_un _ state).
left. auto. apply pure_atom_cmp_eq.
apply listd_merge_un2. apply pure_atom_cmp_eq. simpl; right; auto.
intros; rewrite pure_atom_cmp_eq; auto.
auto.
Qed.

Lemma ef_sound ce c l0 s :
  clause_denote c s -> listd clause_denote inter TT l0 s ->
  listd clause_denote inter TT (ef ce c l0) s.
Proof with auto.
intros H1 H2. unfold ef. destruct ce... destruct c... destruct delta...
destruct p... destruct e... if_tac...
apply ef_aux_sound... simpl; auto. apply var_eq_refl.
Qed.

Lemma remove_trivial_atoms_sound b atms s :
  listd pure_atom_denote inter b atms s ->
  listd pure_atom_denote inter b (remove_trivial_atoms atms) s.
Proof.
intro A; induction atms; auto.
destruct a; simpl in A |- *; destruct A as [A1 A2]; specialize (IHatms A2).
solve [remember (expr_cmp e e0) as b'; destruct b'; simpl; try split; auto].
Qed.

Lemma remove_trivial_atoms_equiv b atms s :
  listd pure_atom_denote inter b (remove_trivial_atoms atms) s <->
  listd pure_atom_denote inter b atms s.
Proof.
split; intro A;
[ |solve[apply remove_trivial_atoms_sound; auto]].
induction atms; auto; destruct a; simpl in A |- *.
remember (expr_cmp e e0) as b'; destruct b'; simpl in A;
[ |solve[destruct A as [A1 A2]; specialize (IHatms A2); split; auto]
  |solve[destruct A as [A1 A2]; specialize (IHatms A2); split; auto]].
apply comp_eq in Heqb'; auto. subst e0.
specialize (IHatms A).
split; auto.
solve[apply var_eq_refl].
Qed.

Lemma delete_resolved_sound c s :
  clause_denote c s -> clause_denote (delete_resolved c) s.
Proof with simpl; auto.
intro H1. destruct c... intros H2.
(*2: intros; left; unfold var_eq; auto.
2: intros; left; unfold var_eq; auto.*)
rewrite (@listd_sort_uniq_inter _ state), remove_trivial_atoms_equiv in H2.
rewrite (@listd_sort_uniq_un _ state). apply (H1 H2).
intros x y; rewrite <-pure_atom_cmp_eq; auto.
intros x y; rewrite <-pure_atom_cmp_eq; auto.
Qed.

Lemma rewrite_by_eqv s t atm st :
  (s === t) st ->
  pure_atom_denote atm st = pure_atom_denote (rewrite_by s t atm) st.
Proof with simpl; auto.
intro H1. apply prop_ext; split. intro H2.
destruct atm as [e1 e2]. simpl.
remember (expr_eq s e1) as b1; remember (expr_eq s e2) as b2.
destruct b1. destruct b2...
assert (H3: (t === t) st) by (apply var_eq_refl). if_tac...
assert (H3: (t === e2) st).
  apply var_eq_trans with (y := s). apply var_eq_sym...
  apply expr_eq_eq' in Heqb1; subst s.
  apply var_eq_trans with (y := e1)... apply var_eq_refl.
if_tac... apply var_eq_sym...
destruct b2...
assert (H3: (e1 === t) st).
  apply var_eq_trans with (y := e2)...
  apply var_eq_trans with (y := s)...
  apply expr_eq_eq' in Heqb2; subst s. apply var_eq_refl.
if_tac... apply var_eq_sym...
(* <-- *)
intro H2; destruct atm as [e1 e2]. simpl.
 simpl in H2. remember (expr_eq s e1) as b1; remember (expr_eq s e2) as b2.
destruct b1. destruct b2... if_tac in H2.
apply expr_eq_eq' in Heqb1. apply expr_eq_eq' in Heqb2.
subst. subst e1. apply var_eq_refl.
apply expr_eq_eq' in Heqb1. apply expr_eq_eq' in Heqb2.
subst. subst e1. apply var_eq_refl.
apply expr_eq_eq' in Heqb1. subst s. simpl in H2. if_tac in H2.
simpl in H2. apply var_eq_trans with (y := t)... apply var_eq_sym...
simpl in H2.  apply var_eq_trans with (y := t)... apply var_eq_sym...
simpl in H2. destruct b2. apply expr_eq_eq' in Heqb2. subst s.
if_tac in H2; simpl in H2.
apply var_eq_trans with (y := t)...
apply var_eq_trans with (y := t)... apply var_eq_sym...
simpl in H2. apply var_eq_sym...
Qed.

Lemma rewrite_by_sound s t atm st :
  (s === t) st -> pure_atom_denote atm st ->
  pure_atom_denote (rewrite_by s t atm) st.
Proof with simpl; auto.
intro H1; rewrite <-rewrite_by_eqv...
Qed.

Lemma rewrite_by_complete s t atm st :
  (s === t) st -> pure_atom_denote (rewrite_by s t atm) st ->
  pure_atom_denote atm st.
Proof with simpl; auto. intro H1; rewrite <-rewrite_by_eqv... Qed.

Lemma clause_denote_foldl (f: clause -> clause -> clause) l c0 s :
  listd clause_denote inter TT l s -> clause_denote c0 s ->
  (forall c d, clause_denote c s -> clause_denote d s ->
               clause_denote (f c d) s) ->
  clause_denote (fold_left f l c0) s.
Proof with simpl; auto.
intros H1 H2 H3. revert c0 H2. induction l... intros c0 H2.
inversion H1; apply IHl...
Qed.

Lemma rewrite_expr_eqv s t u st : (s === t) st -> (u === rewrite_expr s t u) st.
Proof.
intros H. unfold rewrite_expr. remember (expr_eq s u) as b. if_tac.
apply expr_eq_eq' in Heqb. rewrite <-Heqb; auto.
apply var_eq_refl.
Qed.

(* put this lemma elsewhere *)

Lemma var_eq_join_sub e1 e2 (x y s : state) :
  sepalg.join x y s -> ((e1 === e2) s <-> (e1 === e2) x).
Proof.
inversion 1. inversion H0. unfold var_eq, expr_denote in *.
rewrite H2, H3. split; auto.
Qed.

Lemma rewrite_clause_in_space_sound a b p1 p2 sigma0 st :
  clause_denote (PureClause nil [Eqv a b] p1 p2) st ->
  space_denote sigma0 st ->
  space_denote (map (rewrite_clause_in_space (PureClause nil [Eqv a b] p1 p2))
    sigma0) st.
Proof with simpl; auto; try solve[congruence].
intros H1 H2. unfold space_denote. revert st H1 H2; induction sigma0...
intros st H1 H2. simpl in H2. destruct H2 as [x [y [H2 [H3 H4]]]].
exists x; exists y. split; auto. split; auto.
unfold rewrite_clause_in_space.
unfold rewrite_in_space. destruct a0; simpl in *.
rewrite <-rewrite_expr_eqv. rewrite <-rewrite_expr_eqv. auto.
spec H1; auto. inversion H1. rewrite <-var_eq_join_sub; eauto. inversion H.
spec H1; auto. inversion H1. rewrite <-var_eq_join_sub; eauto. inversion H.
rewrite <-rewrite_expr_eqv. rewrite <-rewrite_expr_eqv. auto.
spec H1; auto. inversion H1. rewrite <-var_eq_join_sub; eauto. inversion H.
spec H1; auto. inversion H1. rewrite <-var_eq_join_sub; eauto. inversion H.
apply IHsigma0...
spec H1; auto. inversion H1. left; rewrite <-var_eq_join_sub; eauto.
inversion H.
Qed.

Lemma rewrite_in_space_eqv e1 e2 a st :
  (e1 === e2) st ->
  (space_atom_denote (rewrite_in_space e1 e2 a) st <-> space_atom_denote a st).
Proof with simpl; auto.
unfold rewrite_in_space. intros H1. split.
destruct a...
rewrite <-rewrite_expr_eqv; auto. rewrite <-rewrite_expr_eqv; auto.
rewrite <-rewrite_expr_eqv; auto. rewrite <-rewrite_expr_eqv; auto.
destruct a...
rewrite <-rewrite_expr_eqv; auto. rewrite <-rewrite_expr_eqv; auto.
rewrite <-rewrite_expr_eqv; auto. rewrite <-rewrite_expr_eqv; auto.
Qed.

Lemma rewrite_in_space_sound e1 e2 sigma0 st :
  (e1 === e2) st ->
  space_denote sigma0 st ->
  space_denote (map (rewrite_in_space e1 e2) sigma0) st.
Proof with simpl; auto; try solve[congruence].
intros H1 H2. unfold space_denote. revert st H1 H2; induction sigma0...
intros st H1 H2. simpl in H2. destruct H2 as [x [y [H2 [H3 H4]]]].
exists x; exists y. split; auto. split; auto.
rewrite rewrite_in_space_eqv... rewrite <-var_eq_join_sub; eauto.
apply IHsigma0... rewrite <-var_eq_join_sub; eauto.
Qed.

Lemma demodulate_sound c d s :
  clause_denote c s -> clause_denote d s -> clause_denote (demodulate c d) s.
Proof with simpl; auto.
intros H1 H2. destruct c... destruct gamma, delta...
 destruct p... destruct delta...
destruct d... intro H3.
simpl in H1; spec H1; auto. inversion H1. 2: inversion H. clear H1. subst priority0.
induction gamma. simpl in H2; spec H2; auto. induction delta...
inversion H2. left. apply rewrite_by_sound... right. apply IHdelta...
destruct H3 as [H3 H4]. apply IHgamma... intro H5. simpl in H2; spec H2.
split... rewrite <-rewrite_by_eqv in H3... auto.
induction gamma. simpl in H2; spec H2; auto. induction delta...
simpl in H2. intros _.
apply rewrite_in_space_sound; auto.
simpl in H1. spec H1; auto. inversion H1... inversion H.
simpl in H2. intros _. inversion H2.
left. apply rewrite_by_sound; auto.
simpl in H1. spec H1; auto. inversion H1... inversion H0.
right. rewrite (@listd_unfold_un _ state).
rewrite (@listd_unfold_un _ state) in H. inversion H.
  left. clear - H0 H1. induction delta...
  simpl in H0. destruct H0. left. apply rewrite_by_sound...
  simpl in H1. spec H1... inversion H1... inversion H0.
  right. apply IHdelta...
  right. apply rewrite_in_space_sound...
  simpl in H1. spec H1; auto. inversion H1... inversion H3.
intros. apply IHgamma... intros H3.
assert (H4: pure_atom_denote a s).
  simpl in H. destruct H as [H4 H5].
  apply rewrite_by_complete in H4...
  simpl in H1. spec H1; auto. destruct H1... inversion H.
simpl in H2. spec H2; auto. split... (*apply H2.*)
apply listd_map_pred with (f:=pure_atom_denote).
intros a' H3. apply rewrite_by_sound...
  simpl in H1. spec H1; auto. inversion H1... inversion H0.
simpl in H. destruct H as [H3 H4].
simpl in H1. spec H1; auto. destruct H1 as [H5|H5]; [|inversion H5].
clear - H3 H4 H5. induction gamma...
split... eapply rewrite_by_complete; eauto.
simpl in H4. destruct H4...
simpl in H4. destruct H4...
(* NegSpaceClause case *)
rewrite (@listd_unfold_inter _ state). intros [H3 H4].
cut (listd pure_atom_denote un FF delta s).
  intros H5. simpl in H1. spec H1; auto. destruct H1 as [H6|H6]; [|inversion H6].
  clear - H5 H6. induction delta... simpl in H5. inversion H5.
  left. apply rewrite_by_sound... right...
apply H2. rewrite (@listd_unfold_inter _ state). split.
simpl in H1; spec H1; auto. destruct H1 as [H5|H5]; [|inversion H5].
clear - H3 H5. induction gamma...
simpl in H3; destruct H3 as [H3 H4]. split...
eapply rewrite_by_complete; eauto.
simpl in H1; spec H1; auto. destruct H1 as [H5|H5]; [|inversion H5].
clear - H4 H5. revert s H4 H5. induction sigma...
intros s H4 H5. simpl in H4. destruct H4 as [x [y [H4 [H6 H7]]]].
exists x; exists y. apply rewrite_in_space_eqv in H6...
split... split... apply IHsigma... rewrite <-var_eq_join_sub; eauto.
rewrite <-var_eq_join_sub; eauto.
Qed.

Lemma simplify_sound l c s :
  listd clause_denote inter TT l s -> clause_denote c s ->
  clause_denote (simplify l c) s.
Proof with simpl; auto.
intros H1 H2. unfold simplify. apply delete_resolved_sound.
apply clause_denote_foldl...
intros c0 d H3 H4; apply demodulate_sound...
Qed.

Lemma space_denote_foldl
  (f: list space_atom -> clause -> list space_atom) l sigma0 s :
    listd clause_denote inter TT l s -> space_denote sigma0 s ->
    (forall c sigma, clause_denote c s -> space_denote sigma s ->
                 space_denote (f sigma c) s) ->
  space_denote (fold_left f l sigma0) s.
Proof with simpl; auto.
intros H1 H2 H3. revert sigma0 H2. induction l... intros sigma0 H2.
inversion H1; apply IHl...
Qed.

Lemma space_denote_map_id sigma0 st :
  space_denote sigma0 st ->
  space_denote (map (fun atm : space_atom => atm) sigma0) st.
Proof.
revert st. induction sigma0. auto.
simpl. intros st [x [y [H1 [H2 H3]]]].
exists x; exists y; split; auto.
Qed.

Lemma simplify_atoms_sound l sigma st :
  listd clause_denote inter TT l st -> space_denote sigma st ->
  space_denote (simplify_atoms l sigma) st.
Proof with simpl; auto; try solve[congruence].
intros H1 H2. unfold simplify_atoms.
apply space_denote_foldl...
intros c sigma0 H3 H4.
destruct c. destruct gamma. destruct delta.
unfold rewrite_clause_in_space... apply space_denote_map_id...
destruct delta. destruct p. apply rewrite_clause_in_space_sound; auto.
destruct p; unfold rewrite_clause_in_space... apply space_denote_map_id...
destruct p; unfold rewrite_clause_in_space... apply space_denote_map_id...
unfold rewrite_clause_in_space... apply space_denote_map_id...
unfold rewrite_clause_in_space... apply space_denote_map_id...
Qed.

Lemma infer_list_sound ce c l s :
  clause_denote c s -> listd clause_denote inter TT l s ->
  listd clause_denote inter TT (infer ce c l) s.
Proof with simpl; auto.
intros A B; unfold infer. autounfold with DEBUG_UNFOLD.
rewrite (@listd_sort_uniq_inter _ state).
2: intros; rewrite <-compare_clause_eq with (cl1 := x)...
apply listd_filter_pred.
apply listd_map_pred with (f := clause_denote).
solve[intros d H1; apply simplify_sound; simpl; auto].
apply ef_sound... apply listd_fold_left... intros d cls H1 H2. apply sp_sound...
Qed.

Lemma clause_generate_sound R c c' v e s :
  clause_denote c s -> clause_generate R c = inl _ (v, e, c') ->
  clause_denote c' s.
Proof with try solve [simpl; auto|congruence].
intros. unfold clause_generate in H0.
destruct c... destruct delta... destruct p... destruct e0...
if_tac in H0... if_tac in H0... if_tac in H0...
Qed.

Lemma partial_mod_sound1 R R' acc l l' s :
  listd clause_denote inter TT l s -> listd clause_denote inter TT acc s ->
  partial_mod R acc l = inl _ (R', l') ->
  listd clause_denote inter TT l' s.
Proof with try solve [simpl; auto|congruence].
intros. revert acc R H0 H1. induction l.
intros acc R H0 H1. simpl in H1; inversion H1; subst...
intros acc R H0 H1. simpl in H; destruct H.
simpl in H1. destruct a. if_tac in H1.
inversion H1; subst. apply IHl with (R:=R)(acc:=acc)...
remember (clause_generate R (PureClause gamma delta priority prio_ok)) as b.
destruct b. destruct p. destruct p. apply IHl with (R:=(v,e)::R)(acc:=c::acc)...
simpl. split. eapply clause_generate_sound; eauto. auto.
congruence. inversion H1; subst... inversion H1; subst...
Qed.

Lemma partial_mod_sound2 R R' acc l c ce s :
  listd clause_denote inter TT l s -> listd clause_denote inter TT acc s ->
  partial_mod R acc l = inr _ (R', c, ce) -> clause_denote c s.
Proof with try solve [simpl; auto|congruence].
intros. revert acc R H0 H1. induction l.
intros acc R H0 H1. simpl in H1; inversion H1; subst...
intros acc R H0 H1. simpl in H; destruct H.
simpl in H1. destruct a. if_tac in H1.
inversion H1; subst. apply IHl with (R:=R)(acc:=acc)...
remember (clause_generate R (PureClause gamma delta priority prio_ok)) as b.
destruct b. destruct p. destruct p. apply IHl with (R:=(v,e)::R)(acc:=c0::acc)...
simpl. split. eapply clause_generate_sound; eauto. auto.
inversion H1; subst... congruence. inversion H1; subst...
Qed.

Lemma main_sound n l r units0 units given unselected s :
  listd clause_denote inter TT l s ->
  listd clause_denote inter TT units0 s ->
  main n units0 l = (r, units, given, unselected) ->
  setd clause_denote inter TT given s /\ listd clause_denote inter TT units s.
Proof with try solve[simpl; auto].
apply main_ind.
intros. inversion H1. split; solve[apply setd_empty_set|subst; auto].
intros. inversion H1. split; solve[apply setd_empty_set|subst; auto].
intros; inversion H1; subst; clear H1.
assert (H3 : listd clause_denote inter TT l' s).
  unfold l'. apply listd_filter_pred. autounfold with DEBUG_UNFOLD.
  apply listd_partition_pred with (f := clause_denote) (s0 := s) in e1...
  destruct e1. apply listd_map_pred with (f := clause_denote)...
  intros; apply simplify_sound...
  unfold us'; apply cclose_sound...
apply partial_mod_sound1 with (s:=s) in e2...
split; unfold clause_list2set; [apply setd_fold_left|]...
2: apply setd_empty_set.
solve[intros; apply setd_add; auto].
assert (H4 : listd clause_denote inter TT us s /\
             listd clause_denote inter TT rs s)
  by (eapply listd_partition_pred; eauto).
destruct H4 as [H4 H5].
apply cclose_sound...
rewrite listd_app, (@listd_unfold_inter _ state); split...
unfold us'; apply cclose_sound...
intros until r0; intros IH H1 H2; apply IH...
autounfold with DEBUG_UNFOLD.
rewrite (@listd_sort_inter _ state).
assert (H3 : listd clause_denote inter TT l' s).
  unfold l'. apply listd_filter_pred. autounfold with DEBUG_UNFOLD.
  apply listd_partition_pred with (f := clause_denote) (s0 := s) in e1...
  destruct e1. apply listd_map_pred with (f := clause_denote)...
  intros; apply simplify_sound...
  unfold us'; apply cclose_sound...
rewrite listd_app, (@listd_unfold_inter _ state); split...
apply infer_list_sound...
apply partial_mod_sound2 with (R:=nil)(R':=R)(acc:=nil)(l:=l')(ce:=cty)...
apply cclose_sound.
rewrite listd_app, (@listd_unfold_inter _ state); split...
  apply listd_partition_pred with (h := is_unit_clause) (xs:=us)(ys:=rs) in H1...
  destruct H1... unfold us'; apply cclose_sound...
Qed.

Lemma main_Cexample_sound n l R sel units given unselected s :
  listd clause_denote inter TT l s ->
  main n nil l = (C_example R sel, units, given, unselected) ->
  setd clause_denote inter TT sel s.
Proof with try solve[simpl; auto|congruence].
apply main_ind.
intros. inversion H0. intros...
intros; inversion H0; subst; clear H0.
assert (H3 : listd clause_denote inter TT l' s).
  unfold l'. apply listd_filter_pred. autounfold with DEBUG_UNFOLD.
  apply listd_partition_pred with (f := clause_denote) (s0 := s) in e1...
  destruct e1. apply listd_map_pred with (f := clause_denote)...
  intros; apply simplify_sound...
  unfold us'; apply cclose_sound...
apply partial_mod_sound1 with (s:=s) in e2...
unfold clause_list2set; apply setd_fold_left... 2: apply setd_empty_set.
solve[intros; apply setd_add; auto].
intros. apply H...
autounfold with DEBUG_UNFOLD.
rewrite (@listd_sort_inter _ state).
assert (H3 : listd clause_denote inter TT l' s).
  unfold l'. apply listd_filter_pred. autounfold with DEBUG_UNFOLD.
  apply listd_partition_pred with (f := clause_denote) (s0 := s) in e1...
  destruct e1. apply listd_map_pred with (f := clause_denote)...
  intros; apply simplify_sound...
  unfold us'; apply cclose_sound...
rewrite listd_app, (@listd_unfold_inter _ state); split...
apply infer_list_sound...
apply partial_mod_sound2 with (R:=nil)(R':=R0)(acc:=nil)(l:=l')(ce:=cty)...
Qed.

Lemma empty_clause_False c s :
  is_empty_clause c = true -> ~(clause_denote c s).
Proof with try solve[congruence].
unfold is_empty_clause; destruct c... destruct gamma, delta...
simpl. firstorder.
Qed.

Lemma main_Valid_empty_clause n l units final empty s :
  listd clause_denote inter TT l s ->
  ~(main n nil l = (Valid, units, final, empty)).
Proof with try solve[simpl; auto|congruence].
apply main_ind...
intros. exfalso. rewrite existsb_exists in e0. destruct e0 as [x [H1 H2]].
assert (H' : listd clause_denote inter TT (map delete_resolved l0) s).
  eapply listd_map_pred; eauto. solve[intros; apply delete_resolved_sound; auto].
apply listd_In_inv_pred with (a:=x) in H'... eapply empty_clause_False; eauto.
intros. apply H.
autounfold with DEBUG_UNFOLD.
rewrite (@listd_sort_inter _ state).
assert (H3 : listd clause_denote inter TT l' s).
  unfold l'. apply listd_filter_pred. autounfold with DEBUG_UNFOLD.
  apply listd_partition_pred with (f := clause_denote) (s0 := s) in e1...
  destruct e1. apply listd_map_pred with (f := clause_denote)...
  intros; apply simplify_sound...
  unfold us'; apply cclose_sound...
rewrite listd_app, (@listd_unfold_inter _ state); split...
apply infer_list_sound...
apply partial_mod_sound2 with (R:=nil)(R':=R)(acc:=nil)(l:=l')(ce:=cty)...
Qed.

Lemma check_clauseset_Valid_sound init units g u :
  check_clauseset init = (Valid, units, g, u) ->
  setd clause_denote inter TT init |-- clause_denote empty_clause.
Proof with simpl; auto.
unfold check_clauseset; intros H.
intros s H1. unfold setd in H1.
assert (listd clause_denote inter TT
         (print_pures_list (rsort (rev_cmp compare_clause2)
           (M.elements (M.filter not_taut init)))) s).
  autounfold with DEBUG_UNFOLD. rewrite (@listd_sort_inter _ state).
  apply listd_In_pred...
  intros cl H2; rewrite Melements_spec1 in H2.
  rewrite M.filter_spec in H2. destruct H2 as [H2 _].
  apply listd_In_inv_pred with (a:=cl) in H1... rewrite Melements_spec1...
  unfold Morphisms.Proper, Morphisms.respectful; intros ? ? H3; rewrite H3...
clear H1. exfalso. eapply main_Valid_empty_clause with (s:=s); eauto.
Qed.

Lemma check_clauseset_Cexample_sound init units final empty R selected :
  check_clauseset init = (C_example R selected, units, final, empty) ->
  setd clause_denote inter TT init |--
    setd clause_denote inter TT selected &&
    setd clause_denote inter TT final &&
    listd clause_denote inter TT units.
Proof with simpl; auto.
unfold check_clauseset; intros. intros s H1. generalize H as H'; intros.
apply main_sound with (s:=s) in H... destruct H as [H4 H5].
apply main_Cexample_sound with (s:=s) in H'... split; try split; auto.
autounfold with DEBUG_UNFOLD.
rewrite (@listd_sort_inter _ state).
apply listd_In_pred...
intros cl H2; rewrite Melements_spec1 in H2.
rewrite M.filter_spec in H2. destruct H2 as [H2 _]. unfold setd in H1.
apply listd_In_inv_pred with (a:=cl) in H1... rewrite Melements_spec1...
unfold Morphisms.Proper, Morphisms.respectful; intros ? ? H3; rewrite H3...
autounfold with DEBUG_UNFOLD.
rewrite (@listd_sort_inter _ state).
apply listd_In_pred...
intros cl H2; rewrite Melements_spec1 in H2.
rewrite M.filter_spec in H2. destruct H2 as [H2 _]. unfold setd in H1.
apply listd_In_inv_pred with (a:=cl) in H1... rewrite Melements_spec1...
unfold Morphisms.Proper, Morphisms.respectful; intros ? ? H3; rewrite H3...
Qed.

End SP_Sound.
