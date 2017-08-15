Load loadpath.
Require Import ZArith Coq.Lists.List Permutation.
Require Import VST.msl.Axioms VST.msl.predicates_sa VST.veric.Coqlib2.
Require Import veristar.variables veristar.datatypes veristar.clauses
               veristar.list_denote veristar.heapresolve
               veristar.model_type veristar.model
               veristar.clause_lemmas veristar.basic.

Import HeapResolve.

Module Type WF_SOUND.
Declare Module VSM : VERISTAR_MODEL.
Import VSM VeriStarLogic.

Import sepalg.

Axiom do_wellformed_sound : forall cl,
  clause_denote cl |-- setd clause_denote inter TT (do_wellformed cl).

End WF_SOUND.

Module WF_Sound (VSM : VERISTAR_MODEL) : WF_SOUND with Module VSM := VSM.
Module VSM := VSM.
Import VSM VeriStarLogic.

Module CL := CL_Sound VSM. Import CL.

Import sepalg.

Lemma state_join_var_eq : forall (s0 s1 s : state) x y,
  join s0 s1 s -> (x === y) s0 -> (x === y) s.
Proof.
intros; destruct s, s0, s1, H. simpl in *. destruct H.
unfold var_eq in *; subst; auto.
Qed.

Lemma state_join_var_eq' : forall (s0 s1 s : state) x y,
  join s0 s1 s -> (x === y) s -> (x === y) s0.
Proof.
intros; destruct s; destruct s0; destruct s1. destruct H. simpl in *.
destruct H; unfold var_eq in *; subst; auto.
Qed.

Lemma lseg_nil_or_loc : forall x y h, lseg x y h -> nil_or_loc y.
Proof. induction 1; auto. Qed.

(* rule w1 *)

Lemma w_next_nil : forall y Sigma s,
  clause_denote (NegSpaceClause nil (Next Nil y :: Sigma) nil) s.
Proof.
intros. intros [s0 [s1 [Hjoin [H1 _]]]]. simpl in *.
simpl in H1.
rewrite nil_not_loc in H1. contradiction.
Qed.

(* rule w2 *)

Lemma w_lseg_nil : forall y Sigma s,
  clause_denote (NegSpaceClause nil (Lseg Nil y :: Sigma) [Eqv y Nil]) s.
Proof.
intros. intros [s0 [s1 [Hjoin [H1 _]]]].
simpl in H1. simpl in H1. left.
inversion  H1; clear H1; subst.
simpl. eapply state_join_var_eq; eauto.
symmetry; auto. apply var_eq_sym; auto.
exfalso. simpl in H0. rewrite nil_not_loc in H0. inversion H0.
Qed.

Ltac dsepcon :=
match goal with
  [ H : sepcon _ _ _ |- _ ] =>
  let s1 := fresh "s" in
    let s2 := fresh "s" in
      let JOIN := fresh "JOIN" in
        let H1 := fresh "H" in
          let H2 := fresh "H" in
      destruct H as [s1 [s2 [JOIN [H1 H2]]]]
end.

Lemma nil_or_loc_full v : nil_or_loc v -> full v.
Proof.
intros. destruct H.
subst. apply nil_full.
destruct H as [l ?].
apply val2loc_full with l; auto.
Qed.

Hint Resolve nil_or_loc_full.

Lemma expr_denote_heap_ind : forall x s h h',
  expr_denote x (State s h) = expr_denote x (State s h').
Proof. intros. destruct x; auto. Qed.

Lemma next_next_join_False : forall s0 s0' s1 s2 x z1 z2,
  rawnext x z1 s0 -> join_sub s0 s0' ->
  rawnext x z2 s2 -> join_sub s2 s1 ->
  joins s0' s1 -> False.
Proof.
intros s0 s0' s1 s2 x z1 z2 H0 [s3' H9] H2 [s3 H1] [s H] .
destruct (rawnext_at1 (rawnext2rawnext' H0) H9).
destruct (rawnext_at1 (rawnext2rawnext' H2) H1).
destruct (rawnext_at1 H4 H).
apply (rawnext_not_emp H6 H7).
Qed.

Lemma next_in_dom_rawnext sigma x s :
  next_in_dom x sigma = true -> space_denote sigma s ->
  exists s0, exists z, space_atom_denote (Next (Var x) z) s0 /\ join_sub s0 s.
Proof with auto; try congruence; try solve [
  destruct B as [x' [y' [C [D E]]]]; destruct (IHsigma A y' E) as [s0 [z [F G]]];
    subst; exists s0; exists z; split; simpl; auto;
      apply join_sub_trans with (b := y'); simpl; auto;
        eapply join_join_sub'; eauto].
intros A B; revert s B; induction sigma; intros s B. simpl in A...
simpl in A. remember a as b; destruct b... remember e as b'; destruct b'...
destruct (Ident.eq_dec x v)... destruct B as [x' [y' [C [D E]]]].
subst; exists x'; exists e0; split... solve [eapply join_join_sub'; eauto].
Qed.

Lemma nn_njoin sigma x z s1 s2 :
  next_in_dom x sigma = true -> space_denote sigma s1 ->
  space_atom_denote (Next (Var x) z) s2 -> joins s1 s2 ->
  False.
Proof with try congruence.
intros A B C D; destruct (next_in_dom_rawnext _ _ _ A B) as [s' [z' [F G]]].
simpl in F, C. cut (stk s2 = stk s'). intro Heq; rewrite Heq in *; clear Heq.
destruct (val2loc (env_get (stk s') x))...
destruct F as [H I]; destruct C as [J K].
assert (L : join_sub (hp s') (hp s1)).
  destruct G as [x0 [G1 G2]]; exists (hp x0)...
assert (M : joins (hp s1) (hp s2)).
  destruct D as [x0 [D1 D2]]; exists (hp x0)...
generalize (next_next_join_False _ _ (hp s2) _ _ _ _ H L J)... intro N.
apply N... apply join_sub_refl.
destruct G as [? [[G0 G1] G']]; destruct D as [? [[D0 D1] D']].
solve [rewrite G0, G1, D0; auto].
Qed.

Lemma join_stacks_eq : forall s0 s1 s : state,
  join s0 s1 s -> stk s0=stk s1 /\ stk s0=stk s.
Proof.
intros.
destruct H. destruct H.
subst; split; auto.
transitivity (stk s1); auto.
Qed.

Local Notation "'inter'" := (@andp _).

Local Notation "'un'" := (@orp _).

Lemma pure_atomd_pure atm s0 s :
  pure_atom_denote atm s0 -> join_sub s0 s -> pure_atom_denote atm s.
Proof with try solve [simpl; auto | congruence].
intros A B. destruct atm as [e e0]... destruct B as [s1 B]. simpl.
solve [eapply state_join_var_eq; eauto].
Qed.

Lemma listd_pure_atomdi atms s0 s :
  listd pure_atom_denote inter TT atms s0 -> join_sub s0 s ->
  listd pure_atom_denote inter TT atms s.
Proof with simpl; auto.
induction atms... intros [A B] C. split... solve [eapply pure_atomd_pure; eauto].
Qed.

Lemma listd_pure_atomdu atms s0 s :
  listd pure_atom_denote un FF atms s0 -> join_sub s0 s ->
  listd pure_atom_denote un FF atms s.
Proof with simpl; auto.
induction atms... intros [A | A] B.
left; eapply pure_atomd_pure; eauto. right...
Qed.

Lemma listd_pure_atomd_purei atms s0 s :
  listd (fun atms : list pure_atom => listd pure_atom_denote inter TT atms)
      inter TT atms s0 ->
  join_sub s0 s ->
  listd (fun atms : list pure_atom => listd pure_atom_denote inter TT atms)
      inter TT atms s.
Proof with simpl; auto.
induction atms... intros [A B] C. split... eapply listd_pure_atomdi; eauto.
Qed.

Lemma listd_pure_atomd_pureu atms s0 s :
  listd (fun atms : list pure_atom => listd pure_atom_denote un FF atms)
      inter TT atms s0 ->
  join_sub s0 s ->
  listd (fun atms : list pure_atom => listd pure_atom_denote un FF atms)
      inter TT atms s.
Proof with simpl; auto.
induction atms... intros [A B] C. split... eapply listd_pure_atomdu; eauto.
Qed.

Lemma do_well1_2_sound sigma s :
  space_denote sigma s ->
  listd (fun atms => listd pure_atom_denote un FF atms) inter TT
    (do_well1_2 sigma) s.
Proof with try solve [simpl; auto | congruence | inversion 1
  | apply listd_pure_atomd_pureu with (s0 := y);
    [ | exists x; apply join_comm; auto ]; solve [apply IHsigma; auto]].
revert s; induction sigma... intros s H.
remember a as b; destruct b as [e e0 | ]; simpl.
remember e as b1; destruct b1.
generalize (w_next_nil e0 sigma s H)... generalize H; intros [x [y [A [B C]]]]...
remember e as b; destruct b... generalize (w_lseg_nil e0 sigma s H) as A...
intro. inversion A as [B | B]; [ | inversion B ]. split...
generalize H; intros [x [y [C [D E]]]]...
generalize H; intros [x [y [C [D E]]]]...
Qed.

Lemma do_well3_sound sigma s :
  space_denote sigma s ->
  listd (fun atms => listd pure_atom_denote un FF atms) inter TT
    (do_well3 sigma) s.
Proof with try solve [simpl; auto | congruence | inversion 1
  | apply listd_pure_atomd_pureu with (s0 := y);
    [ | exists x; apply join_comm; auto ]; solve [apply IHsigma; auto] ].
revert s; induction sigma... simpl; intros s [x [y [A [B C]]]].
remember a as b; destruct b... remember e as c; destruct c...
remember (next_in_dom v sigma) as d. if_tac... split...
exfalso. symmetry in Heqd. eapply nn_njoin; eauto.
Qed.

Lemma nl_lseg_in_sound x y sigma s1 s2 s :
  space_atom_denote (Next (Var x) y) s1 ->
  space_denote sigma s2 ->
  join s1 s2 s ->
  listd pure_atom_denote inter TT (lseg_in_dom_atoms x sigma) s.
Proof with try solve [simpl; auto; try congruence; try inversion A
  | destruct (join_assoc B (join_comm C)) as [q1 [q2 Q]];
      apply listd_pure_atomdi with (s0 := q1); [ | eexists; eauto ];
        solve [apply IHsigma with (s2 := w2); auto] ].
intros A B C. revert s s2 B C; induction sigma... intros s s2 B C.
simpl in B; destruct B as [w1 [w2 [B [D E]]]]. destruct a...
destruct e... unfold lseg_in_dom_atoms. if_tac...
try unfold Ident.eq in H.
subst x. split...
rewrite <- order_eqv_sound. simpl in A, D.
inversion D; subst. simpl. destruct (join_assoc B (join_comm C)) as [q [Q1 Q2]].
solve [eapply state_join_var_eq; eauto].
cut (stk w1 = stk s1); [ intro Heq; rewrite Heq in * | ].
rewrite H0 in A; destruct A as [A _].
exfalso. destruct B as [_ B]. destruct (join_assoc H3 B) as [q [Q1 Q2]].
eapply next_next_join_False with
  (s0 := h0) (s0' := hp s2) (s2 := hp s1) (s1 := hp s1); eauto.
econstructor; eauto.
apply join_sub_refl.
destruct (join_assoc (join_comm B) (join_comm C)) as [q [Q1 Q2]].
destruct (join_stacks_eq _ _ _ Q1)...
Qed.

Lemma ll_spooky x y z s1 s2 s1' s2' s :
  lseg (env_get (stk s1) x) (expr_denote y s1) (hp s1) ->
  lseg (env_get (stk s1') x) (expr_denote z s1') (hp s1') ->
  join_sub s1 s2 -> join_sub s1' s2' -> join s2 s2' s ->
  (pure_atom_denote (Eqv (Var x) y) || pure_atom_denote (Eqv (Var x) z))%pred s.
Proof with simpl; auto; try solve [congruence
  | left; simpl; unfold var_eq, expr_denote, stack_get; rewrite H;
      solve [unfold expr_denote, stack_get; rewrite Heq, Heq'; auto]].
intros A1 A2 B1 B2 C.
cut (stk s1 = stk s1'); [ intro Heq; rewrite Heq in * | ].
cut (stk s = stk s1'); [ intro Heq'; rewrite <- Heq' in * | ].
inversion A1; inversion A2; subst...
right; simpl; unfold var_eq, expr_denote, stack_get; rewrite H7.
solve [unfold expr_denote, stack_get; rewrite <- Heq'; auto].
cut (x' = x'0); [ intro Heqx; rewrite <- Heqx in *; clear Heqx | ].
exfalso. clear - H1 H3 H9 H11 B1 B2 C.
assert (D : joins s2 s2') by (apply (join_joins C)).
assert (E : join_sub h2 (hp s2')).
  destruct B2 as [sx1 [_ B2]]; destruct (join_assoc H11 B2) as [q [Q1 Q2]].
  solve [exists q; auto].
assert (F : join_sub h0 (hp s2)).
  destruct B1 as [sx1 [_ B1]]; destruct (join_assoc H3 B1) as [q [Q1 Q2]].
  solve [exists q; auto].
apply (next_next_join_False _ _ _ _ _ _ _ H1 F H9 E).
solve [destruct C as [_ C]; exists (hp s); auto].
solve [rewrite H8 in H0; inversion H0; auto].
destruct B2 as [sx B2]; destruct (join_assoc B2 (join_comm C)) as [q [Q1 Q2]].
destruct (join_stacks_eq _ _ _ Q2)...
destruct B1 as [sx1 B1]; destruct B2 as [sx2 B2].
destruct (join_assoc B1 C) as [q [Q1 Q2]].
destruct (join_assoc B2 (join_comm C)) as [q' [Q1' Q2']].
inversion Q2 as [[H1 H2] _]; inversion Q2' as [[H3 H4] _]...
Qed.

Lemma ll_lseg_in_sound x y sigma s1 s2 s :
  space_atom_denote (Lseg (Var x) y) s1 ->
  space_denote sigma s2 ->
  join s1 s2 s ->
  listd (listd pure_atom_denote un FF) inter TT (map (fun a0 =>
    [Eqv (Var x) y, a0]) (lseg_in_dom_atoms x sigma)) s.
Proof with try solve [simpl; auto; try congruence
  | destruct (join_assoc B (join_comm C)) as [q1 [q2 Q]];
      apply listd_pure_atomd_pureu with (s0 := q1); [ | eexists; eauto ];
        solve [apply IHsigma with (s2 := w2); auto]].
intros A B C. revert s s2 B C; induction sigma... intros s s2 B C.
simpl in B; destruct B as [w1 [w2 [B [D E]]]]. destruct a...
destruct e... unfold lseg_in_dom_atoms. if_tac...
try unfold Ident.eq in *. subst x. split...
simpl in A, D. inversion D; subst.
unfold list_denote; rewrite <- union_assoc; left; rewrite <- order_eqv_sound.
eapply (ll_spooky _ _ _ s1 s1 w1 s2 s A D); eauto.
apply join_sub_refl.  econstructor; eauto.
unfold list_denote; rewrite <- union_assoc; left; rewrite <- order_eqv_sound.
eapply (ll_spooky _ _ _ s1 s1 w1 s2 s A D); eauto.
apply join_sub_refl.  econstructor; eauto.
Qed.

Lemma do_well4_5_sound sigma s :
  space_denote sigma s ->
  listd (fun atms => listd pure_atom_denote un FF atms) inter TT
    (do_well4_5 sigma) s.
Proof with simpl; auto; try congruence; try solve [
  apply listd_pure_atomd_pureu with (s0 := y);
    [ | exists x; apply join_comm; auto ]; apply IHsigma; auto].
revert s; induction sigma... intros s [x [y [A [B C]]]].
remember a as b; destruct b. destruct e...
rewrite listd_app, (@listd_unfold_inter _ state); split...
generalize (nl_lseg_in_sound _ _ _ _ _ _ B C A); intro D.
clear - D. set (l := lseg_in_dom_atoms v sigma) in D |- *. induction l...
solve [destruct D as [D E]; split; [ left; auto | ]; apply IHl; auto].
destruct e... remember (lseg_in_dom_atoms v sigma) as l. destruct l...
rewrite listd_app; split... unfold normalize_atoms.
rewrite (@listd_sort_uniq_un _ state) with (cmp := pure_atom_cmp).
2: apply pure_atom_cmp_eq.
generalize (ll_lseg_in_sound _ _ _ _ _ _ B C A); rewrite <- Heql.
intro D. simpl in D. destruct D as [D E]. destruct D as [D | D].
left. rewrite <- order_eqv_sound...
destruct D. right; left. rewrite <- order_eqv_sound... inversion H.
rewrite (@listd_unfold_inter _ state); split...
generalize (ll_lseg_in_sound _ _ _ _ _ _ B C A); rewrite <- Heql.
simpl; intros [D E]. clear - E.
induction l... simpl in E; destruct E as [E F].
split... unfold normalize_atoms. rewrite (@listd_sort_uniq_un _ state).
2: apply pure_atom_cmp_eq.
destruct E as [E | E]. left; rewrite <- order_eqv_sound...
destruct E; [ right; left; rewrite <- order_eqv_sound; auto | inversion H].
Qed.

Lemma do_well_sound sigma s :
  space_denote sigma s ->
  listd (fun atms => listd pure_atom_denote un FF atms) inter TT
    (do_well sigma) s.
Proof with auto.
intro A. unfold do_well. do 2 (rewrite listd_app, (@listd_unfold_inter _ state)).
split. split... apply do_well1_2_sound... rewrite (@listd_unfold_inter _ state).
split. apply do_well3_sound... apply do_well4_5_sound...
Qed.

Lemma factor_hyp_lem gamma delta l s :
  (listd pure_atom_denote inter TT gamma s ->
    listd (fun atms s => listd pure_atom_denote un FF (atms ++ delta) s)
    inter TT l s) ->
  listd
     (fun (atms : list pure_atom) (s' : state) =>
      listd pure_atom_denote inter TT gamma s' ->
      listd pure_atom_denote un FF (atms ++ delta) s') inter TT l s.
Proof with simpl; auto.
intro A; induction l... split. intro B; specialize (A B); simpl in A; destruct A as [A C]...
apply IHl... intro B. specialize (A B). simpl in A; destruct A as [A C]...
Qed.

Lemma factor_hyp_lem_aux delta l s :
  (listd (listd pure_atom_denote un FF) inter TT l ||
    listd pure_atom_denote un FF delta)%pred s ->
  listd (fun atms s' => listd pure_atom_denote un FF (atms ++ delta) s')
    inter TT l s.
Proof with simpl; auto.
intro A. induction l... split. simpl in A; destruct A as [[A B] | ].
rewrite listd_app, (@listd_unfold_un _ state); left...
rewrite listd_app, (@listd_unfold_un _ state); right...
apply IHl... simpl in A; destruct A as [[? ?] | ]. left... right...
Qed.

Lemma do_wellformed_sound cl :
  clause_denote cl |-- setd clause_denote inter TT (do_wellformed cl).
Proof with simpl; auto with typeclass_instances; try congruence.
intros s A. unfold do_wellformed. destruct cl...
apply setd_empty_set.
apply clause_setd_listd.
apply listd_map_pred
  with (f := fun atms s => listd pure_atom_denote inter TT gamma s ->
    listd pure_atom_denote un FF (atms ++ delta) s).
intros l B C. specialize (B C). unfold normalize_atoms.
rewrite (@listd_sort_uniq_un _ state). 2: apply pure_atom_cmp_eq.
rewrite listd_map, listd_app; [ | intros a b'; rewrite <- order_eqv_sound; auto ].
rewrite (@listd_unfold_un _ state).
rewrite listd_app in B; rewrite (@listd_unfold_un _ state) in B...
apply factor_hyp_lem... intro B; specialize (A B)... apply factor_hyp_lem_aux...
rewrite (@listd_unfold_un _ state) in A. destruct A as [A | A].
right... left. apply do_well_sound...
unfold space_denote; rewrite (@listd_sort_sepcon _ state)...
apply setd_empty_set.
Qed.

End WF_Sound.


