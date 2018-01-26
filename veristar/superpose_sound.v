Load loadpath.
Require Import ZArith Coq.Lists.List Permutation.
Require Import VST.msl.Axioms veric.Coqlib2.
Require Import VST.msl.predicates_sa.
Require Import veristar.datatypes veristar.clauses veristar.clause_lemmas
               veristar.list_denote veristar.superpose veristar.basic
               veristar.compare.
Import Superposition.
Require Import veristar.model_type veristar.model.

Module Type SP_SOUND.
Declare Module VSM : VERISTAR_MODEL.
Import VSM VeriStarLogic.

Axiom check_clauseset_Valid_sound: forall init g u,
  check_clauseset init = (Valid, g, u) ->
  setd clause_denote inter TT init |-- clause_denote empty_clause.

Axiom check_clauseset_Cexample_sound: forall init final empty R selected,
  check_clauseset init = (C_example R selected, final, empty) ->
  setd clause_denote inter TT init |--
    setd clause_denote inter TT selected &&
    setd clause_denote inter TT final.

End SP_SOUND.

Module SP_Sound (VSM : VERISTAR_MODEL) : SP_SOUND with Module VSM := VSM.
Module VSM := VSM.
Import VSM VeriStarLogic.

Implicit Arguments list_denote [A T].
Local Notation "'listd'" := list_denote.

Implicit Arguments andp [A].
Local Notation "'inter'" := (@andp _). (*implicit arguments acting weird*)

(* the following five rules (barring reflexivity resolution, which is performed
   during the simplification phase) are collected in rule "sp" *)

Require Import Bool.

Definition positive_superposition (c d : clause) l0 : list clause :=
  match c , d with
  | PureClause nil (Eqv s t :: pos) _ _ ,
    PureClause nil (Eqv s' v :: pos') _ _ =>
    if expr_eq s s' && expr_lt t s && expr_lt v s' &&
       pure_atom_gt1 (Eqv s t) pos && pure_atom_gt1 (Eqv s' v) pos' &&
       pure_atom_gt (Eqv s' v) (Eqv s t)
    then mkPureClause nil (insert_uniq pure_atom_cmp (norm_pure_atom (Eqv t v))
                          (merge pure_atom_cmp pos pos')) :: l0
    else l0
  | _ , _ => l0
  end.

Definition negative_superposition (c d : clause) l0 : list clause :=
  match c , d with
  | PureClause nil (Eqv s t :: pos) _ _,
    PureClause (Eqv s' v :: neg') pos' _ _ =>
    if expr_eq s s' && expr_lt t s && expr_lt v s'
    then mkPureClause (insert_uniq pure_atom_cmp (norm_pure_atom (Eqv t v)) neg')
                      (merge pure_atom_cmp pos pos') :: l0
    else l0
  | _ , _ => l0
  end.

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
    then mkPureClause nil
            (insert_uniq pure_atom_cmp (norm_pure_atom (Eqv s t)) pos)
                :: l0
    else l0
  | _ => l0
  end.

Definition equality_factoring (c : clause) l0 : list clause :=
  match c with
  | PureClause nil (Eqv u v :: Eqv s t :: pos) _ _ =>
    if expr_eq s u && pure_atom_gt (Eqv u v) (Eqv s t)
    then mkPureClause [norm_pure_atom (Eqv v t)]
               (insert_uniq pure_atom_cmp (norm_pure_atom (Eqv u t)) pos) :: l0
    else l0
  | _ => l0
  end.

Lemma positive_superposition_sound c d l0 s :
  clause_denote c s -> clause_denote d s -> listd clause_denote inter TT l0 s ->
  listd clause_denote inter TT (positive_superposition c d l0) s.
Proof with simpl; auto.
intros A B; destruct c as [gamma delta| |]; destruct d as [gamma' delta'| |]...
2: simpl; destruct gamma, delta... 2: destruct p...
2: simpl; destruct gamma, delta... 2: destruct p...
destruct gamma, delta as [|atm delta]...
destruct atm as [e1 e2], delta'... (*destruct p...*) simpl in A; spec A...
destruct gamma'... destruct gamma'... destruct p...
remember (expr_eq e1 e) as b; destruct b. 2: simpl; auto.
if_tac... split... intro H1. specialize (B H1). simpl in B.
rewrite (@listd_insert_uniq_un _ state)... 2: apply pure_atom_cmp_eq.
destruct A as [A|A];destruct B as [B|B]... rewrite <-(expr_eq_eq' _ _ Heqb) in B.
assert (C: (e0 === e2) s) by (eapply var_eq_trans; apply var_eq_sym in B; eauto).
left; if_tac... solve[apply var_eq_sym; auto].
right; apply listd_merge_un2... solve[apply pure_atom_cmp_eq].
right; apply listd_merge_un1... solve[apply pure_atom_cmp_eq].
right; apply listd_merge_un2... solve[apply pure_atom_cmp_eq].
Qed.

Lemma negative_superposition_sound c d l0 s :
  clause_denote c s -> clause_denote d s -> listd clause_denote inter TT l0 s ->
  listd clause_denote inter TT (negative_superposition c d l0) s.
Proof with simpl; auto.
intros A B; destruct c as [gamma delta| |]; destruct d as [gamma' delta'| |]...
2: simpl; destruct gamma, delta... 2: destruct p...
2: simpl; destruct gamma, delta... 2: destruct p...
destruct gamma, delta... destruct p... destruct gamma'... destruct p...
remember (expr_eq e e1) as b; destruct b. 2: simpl; auto.
if_tac; [simpl|simpl; auto]; rewrite interS; simpl. intro H3. split...
rewrite (@listd_insert_uniq_inter _ state)... 2: apply pure_atom_cmp_eq.
intros [H1 H2].
assert ((e2 === e0) s). if_tac in H1; simpl in H1... apply var_eq_sym...
simpl in A; spec A... inversion A.
simpl in B; spec B. split... apply expr_eq_eq' in Heqb; subst e1.
eapply var_eq_trans; eapply var_eq_sym in H; eauto.
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


Lemma equality_factoring_sound c l0 s :
  clause_denote c s -> listd clause_denote inter TT l0 s ->
  listd clause_denote inter TT (equality_factoring c l0) s.
Proof with
simpl; auto;
try solve [simpl; destruct gamma as [|p]; simpl; auto; destruct p; simpl; auto].
intros A; destruct c as [gamma delta| |]... simpl.
destruct gamma... destruct delta... destruct p... destruct delta... destruct p...
remember (expr_eq e1 e) as b; destruct b...
if_tac... simpl; split; auto. intro Hyp.
rewrite (listd_insert_uniq_un pure_atom_denote FF). 2: apply pure_atom_cmp_eq.
destruct Hyp as [B C].
simpl in A; destruct A as [A|[A|A]]; [auto| | |right; auto].
assert (D : (e === e2) s).
  if_tac in B; simpl in B;
  apply (var_eq_trans _ _ _ _ A); [apply var_eq_sym; auto | auto].
solve[left; if_tac; simpl; [apply var_eq_sym; auto | auto]].
assert (D : (e === e2) s).
  rewrite <- (expr_eq_eq' _ _ Heqb) .
  if_tac in B; simpl in B;
  apply (var_eq_trans _ _ _ _ A); [apply var_eq_sym; auto | auto];
    apply var_eq_refl.
solve[left; if_tac; simpl; [apply var_eq_sym; auto | auto]].
Qed.

Lemma sp_sound c d l0 s :
  clause_denote c s -> clause_denote d s -> listd clause_denote inter TT l0 s ->
  listd clause_denote inter TT (sp c d l0) s.
Proof with simpl; auto.
intros H1 H2 H3.
generalize (negative_superposition_sound c d l0 s) as H4; intro.
generalize (positive_superposition_sound c d l0 s) as H5; intro.
generalize (equality_factoring_sound c l0 s) as H6; intro.
generalize (ordered_factoring_sound c l0 s) as H7; intro.
specialize (H4 H1 H2 H3); specialize (H5 H1 H2 H3).
specialize (H6 H1 H3); specialize (H7 H1 H3).
rewrite (@listd_unfold_inter _ state). split...
destruct c, d... simpl in H4, H5, H6.
destruct gamma, delta... destruct p...
destruct gamma0, delta0... destruct p... if_tac... split... intros _.
destruct H5 as [H5 _].
rewrite (@listd_unfold_un _ state). left. apply H5...
Qed.

Lemma superpose_sound c d l0 s :
  clause_denote c s -> clause_denote d s -> listd clause_denote inter TT l0 s ->
  listd clause_denote inter TT (superpose c d l0) s.
Proof with simpl; auto.
intros H1 H2 H3. unfold superpose. apply sp_sound... apply sp_sound...
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
2: intros; left; unfold var_eq; auto.
2: intros; left; unfold var_eq; auto.
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
Proof with simpl; auto.
intro H1; rewrite <-rewrite_by_eqv...
Qed.

Lemma demodulate_sound c d s :
  clause_denote c s -> clause_denote d s ->
  clause_denote (demodulate c d) s.
Proof with simpl; auto.
intros H1 H2. destruct c... destruct gamma, delta...
 destruct p... destruct delta... destruct d... intro H3.
simpl in H1; spec H1; auto.
inversion H1. 2: inversion H. clear H1.
subst priority0.
induction gamma. simpl in H2; spec H2; auto. induction delta...
inversion H2. left. apply rewrite_by_sound... right. apply IHdelta...
destruct H3 as [H3 H4]. apply IHgamma... intro H5. simpl in H2; spec H2.
split... rewrite <-rewrite_by_eqv in H3... auto.
Qed.

Lemma clause_denote_foldl (f: clause -> clause -> clause) l c0 s :
  listd clause_denote inter TT l s -> clause_denote c0 s ->
  (forall c d, clause_denote c s -> clause_denote d s ->
               clause_denote (f c d) s) ->
  clause_denote (fold_left f l c0) s.
Proof with simpl; auto.
intros H1 H2 H3. revert c0 H2. induction l... intros c0 H2.
inversion H1; apply IHl...
Qed.

Lemma simplify_sound l c s :
  listd clause_denote inter TT l s -> clause_denote c s ->
  clause_denote (simplify l c) s.
Proof with simpl; auto.
intros H1 H2. unfold simplify. apply delete_resolved_sound.
apply clause_denote_foldl...
intros c0 d H3 H4; apply demodulate_sound...
Qed.

Lemma infer_list_sound c l s :
  clause_denote c s -> listd clause_denote inter TT l s ->
  listd clause_denote inter TT (infer_list c l) s.
Proof with simpl; auto.
intros A B; unfold infer_list. autounfold with DEBUG_UNFOLD.
apply listd_filter_pred.
apply listd_map_pred with (f := clause_denote).
solve[intros d H1; apply simplify_sound; auto].
apply listd_fold_left... intros d cls H1 H2.
apply superpose_sound...
Qed.

Lemma insert_uniq_In {A} cmp (l : list A) a a' :
  In a' (insert_uniq cmp a l) -> a = a' \/ In a' l.
Proof with auto.
revert a'; induction l... intro a'. simpl. destruct (cmp a a0)...
simpl; intros [B | B]... specialize (IHl a' B). destruct IHl...
Qed.

Lemma rsort_uniq_In {A} cmp (l : list A) a : In a (rsort_uniq cmp l) -> In a l.
Proof with simpl; auto.
revert a; induction l; intro a'... intro B.
cut (a = a' \/ In a' (rsort_uniq cmp l)); [intro C|].
destruct C... eapply insert_uniq_In; eauto.
Qed.

Lemma pick_In (cls : M.t) cl :
  M.min_elt cls = Some cl -> In cl (M.elements cls).
Proof with try inversion 1; auto.
unfold setd.
remember (M.min_elt cls) as b. destruct b... symmetry in Heqb.
apply M.min_elt_spec1 in Heqb; rewrite <- M.elements_spec1 in Heqb.
rewrite SetoidList.InA_alt in Heqb. destruct Heqb as [y [B C]].
subst. subst. auto.
Qed.

Lemma pick_sound (cls : M.t) c s :
  setd clause_denote inter TT cls s -> M.min_elt cls = Some c ->
  clause_denote c s.
Proof with try inversion 1; auto.
intro A. remember (M.min_elt cls) as b. destruct b...
eapply listd_In_inv_pred; eauto. solve[rewrite Heqb in H; eapply pick_In; eauto].
Qed.

Lemma setd_mem_add c cls cls' s :
  clause_denote c s -> setd clause_denote inter TT cls s ->
  mem_add c cls = Some cls' ->
  setd clause_denote inter TT cls' s.
Proof.
intros H1 H2 H3. rewrite mem_add_spec in H3. if_tac in H3; [congruence|].
inversion H3; subst. apply setd_add; auto.
Qed.

Lemma one_inference_step_sound given unselected given' unselected' s :
  setd clause_denote inter TT given s ->
  setd clause_denote inter TT unselected s ->
  one_inference_step (given, unselected) = (given', unselected') ->
  setd clause_denote inter TT given' s /\
  setd clause_denote inter TT unselected' s.
Proof with simpl; auto.
unfold one_inference_step; intros A B C.
(*DEBUGGING*)
autounfold with DEBUG_UNFOLD in *.
(*DEBUGGING*)
remember (M.delete_min unselected) as b. destruct b as [[c unselected'']| ].
2: inversion C; subst; split; auto.
symmetry in Heqb.
apply M.delete_min_spec1 in Heqb.
  destruct Heqb as [Heqb ?]. subst unselected''.
remember (mem_add (simplify (M.elements given) c) given) as q.
  destruct q as [new_given|].
if_tac in C. inversion C; subst. split. clear C.
symmetry in Heqq; eapply setd_mem_add with (cls := given); eauto.
apply simplify_sound; auto. eapply pick_sound; eauto.
apply setd_fold_left...
clear C. intros until s0. intros H1 H2. if_tac... solve[apply setd_add; auto].
apply infer_list_sound... apply simplify_sound... eapply pick_sound; eauto.
apply setd_remove; auto.
inversion C; subst; split; auto. apply setd_remove; auto.
if_tac in C; inversion C; subst. split; auto. apply setd_remove; auto.
split; auto. apply setd_remove; auto.
Qed.

Lemma simple_loop_induction (P : M.t*M.t -> Prop)
                            given unselected r given' unselected' :
  (forall g u g' u',
    P (g, u) ->
    one_inference_step (g, u) = (g', u') -> P (g', u')) ->
  P (given, unselected) ->
  loop (given, unselected) = (r, given', unselected') -> P (given', unselected').
Proof.
set (P' := fun (g_u : M.t * M.t) (res: superposition_result * M.t*M.t) =>
                P g_u ->
                P (snd (fst res), snd res)).
generalize (loop_ind P'). intros H1 H2. unfold P' in H1. intros H3 H4.
assert (given' = snd (fst (loop (given, unselected)))) as -> by (rewrite H4; auto).
assert (unselected' = snd (loop (given, unselected))) as -> by (rewrite H4; auto).
apply H1; auto; intros ? ? ? ?; inversion 1; subst; auto;
                   intros ? ? H7 _; simpl; [intros R sel ? H8|intro H8].
solve[apply (H2 _ _ _ _ H8 H7); auto].
solve[intros H10; apply H8; auto; apply (H2 _ _ _ _ H10 H7); auto].
Qed.

Lemma loop_sound given unselected given' unselected' r s :
  setd clause_denote inter TT given s ->
  setd clause_denote inter TT unselected s ->
  loop (given, unselected) = (r, given', unselected') ->
  setd clause_denote inter TT given' s /\
  setd clause_denote inter TT unselected' s.
Proof.
intros H1 H2.
set (P := fun (g_u: M.t*M.t) =>
               setd clause_denote inter TT (fst g_u) s /\
               setd clause_denote inter TT (snd g_u) s).
generalize (simple_loop_induction P). unfold P; intros H3.
specialize (H3 given unselected r given' unselected').
intros H4. apply H3; auto.
intros ? ? ? ? [? ?] ?; apply one_inference_step_sound
      with (given := g) (unselected := u); auto.
Qed.

Lemma loop_Valid_empty_clause g u g' u' :
  loop (g, u) = (Valid, g', u') -> M.In empty_clause g' \/ M.In empty_clause u'.
Proof.
set (P' := fun (g_u : M.t * M.t) (res: superposition_result * M.t*M.t) =>
              res = (Valid, g', u') ->
              M.In empty_clause g' \/ M.In empty_clause u').
generalize (loop_ind P'). intros H1 H2. unfold P' in H1.
apply H1 with (given_unselected := (g, u)); auto; intros [? ?] ? ?;
  inversion 1; subst.
autounfold with DEBUG_UNFOLD.
intros H3; inversion 1; subst. rewrite orb_true_iff in H3.
inversion H3 as [H4|H4]; rewrite M.mem_spec in H4; auto.
congruence.
Qed.

Lemma clauses_gen_sound1 R R' cs cs' s :
  listd clause_denote inter TT cs s -> clauses_generate R cs = (R', cs') ->
  setd clause_denote inter TT cs' s.
Proof with simpl; auto; try congruence.
revert R R' cs'; induction cs...
 intros. inversion H0; clear H0; subst. apply setd_empty_set.
intros R R' cs'; destruct (clause_generate R a); intros [A B].
destruct p; destruct p; intro C.
remember (clauses_generate ((v, e) :: R) cs) as h; destruct h.
inversion C; subst. clear C.
apply setd_add; auto.
solve [apply IHcs with (R := (v, e) :: R) (R' := R'); auto].
solve [apply IHcs; auto].
Qed.

Lemma loop_Cexample_model given unselected given' unselected' R sel :
  loop (given, unselected) = (C_example R sel, given', unselected') ->
  (R, sel) = clauses_generate nil
    (rsort_uniq (rev_cmp compare_clause) (M.elements given')).
Proof with try congruence.
set (P' := fun (g_u : M.t * M.t) (res: superposition_result * M.t*M.t) =>
              res = (C_example R sel, given', unselected') ->
  (R, sel) = clauses_generate nil
    (rsort_uniq (rev_cmp compare_clause) (M.elements given'))).
generalize (loop_ind P'). intros H1 H2. unfold P' in H1.
apply H1 with (given_unselected := (given, unselected)); auto; intros [? ?] ? ?;
  inversion 1; subst...
Qed.

Lemma loop_Cexample_sel g u g' u' s R sel :
  setd clause_denote inter TT g s ->
  setd clause_denote inter TT u s ->
  loop (g, u) = (C_example R sel, g', u') ->
  setd clause_denote inter TT sel s.
Proof.
intros H1 H2 H3. generalize H3 as H3'; intro.
apply loop_Cexample_model in H3. symmetry in H3.
apply clauses_gen_sound1 with (s:=s) in H3; auto. clear H3.
rewrite (@listd_sort_uniq_inter _ state).
apply loop_sound with (s:=s) in H3'; destruct H3'; auto.
intros x y; apply rev_cmp_eq. apply compare_clause_eq.
Qed.

Lemma loop_Valid_sound given unselected given' unselected' s :
  setd clause_denote inter TT given s ->
  setd clause_denote inter TT unselected s ->
  loop (given, unselected) = (Valid, given', unselected') ->
  clause_denote empty_clause s.
Proof.
intros H1 H2 H3. generalize H3 as H3'; intro.
apply loop_Valid_empty_clause in H3.
inversion H3 as [H7|H7]; rewrite <-elements_In in H7.
destruct (loop_sound _ _ _ _ _ _ H1 H2 H3') as [H0 H].
apply (listd_In_inv_pred _ _ _ _ H0 H7).
destruct (loop_sound _ _ _ _ _ _ H1 H2 H3') as [H0 H].
apply (listd_In_inv_pred _ _ _ _ H H7).
Qed.

Lemma loop_Cexample_sound given unselected given' unselected' s R selected :
  setd clause_denote inter TT given s ->
  setd clause_denote inter TT unselected s ->
  loop (given, unselected) = (C_example R selected, given', unselected') ->
  setd clause_denote inter TT selected s /\
  setd clause_denote inter TT given' s.
Proof.
intros H1 H2 H3; destruct (loop_sound _ _ _ _ _ _ H1 H2 H3) as [H0 H].
split; auto; apply loop_Cexample_sel with (s:=s) in H3; auto.
Qed.

Lemma check_clauseset_Valid_sound init g u :
  check_clauseset init = (Valid, g, u) ->
  setd clause_denote inter TT init |-- clause_denote empty_clause.
Proof.
unfold check_clauseset; intros C s B.
generalize (setd_empty_set _ clause_denote s); intro A.
assert (H: setd clause_denote inter TT (M.filter not_taut init) s) by
  (apply setd_filter; auto).
apply (loop_Valid_sound _ _ _ _ _ A H C).
Qed.

Lemma check_clauseset_Cexample_model init final empty R selected :
  check_clauseset init = (C_example R selected, final, empty) ->
  (R, selected) = clauses_generate nil
    (rsort_uniq (rev_cmp compare_clause) (M.elements final)).
Proof. solve[unfold check_clauseset; apply loop_Cexample_model]. Qed.

Lemma check_clauseset_Cexample_sound init final u R selected :
  check_clauseset init = (C_example R selected, final, u) ->
  setd clause_denote inter TT init |--
    setd clause_denote inter TT selected &&
    setd clause_denote inter TT final.
Proof.
unfold check_clauseset; intros C s B.
generalize (setd_empty_set _ clause_denote s); intro A.
assert (H: setd clause_denote inter TT (M.filter not_taut init) s) by
  (apply setd_filter; auto).
destruct (loop_Cexample_sound _ _ _ _ _ _ _ A H C). split; auto.
Qed.

End SP_Sound.
