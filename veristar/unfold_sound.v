Load loadpath.
Require Import ZArith Coq.Lists.List Permutation.
Require Import VST.msl.Axioms.
Require Import VST.msl.predicates_sa.
Require Import VST.veric.Coqlib2.
Require Import veristar.variables veristar.datatypes veristar.clauses
               veristar.list_denote veristar.clause_lemmas veristar.heapresolve
               veristar.model_type veristar.model veristar.spred_lemmas
               veristar.clausify_sound veristar.basic veristar.compare.

Require Import Classical.
Import HeapResolve.

Module Type UF_SOUND.
Declare Module VSM : VERISTAR_MODEL.
Import VSM VeriStarLogic.

Axiom unfolding_sound : forall c1 c2 s,
  clause_denote c1 s -> clause_denote c2 s ->
  setd clause_denote inter TT (unfolding c1 c2) s.

End UF_SOUND.

Module UF_Sound (VSM : VERISTAR_MODEL) : UF_SOUND with Module VSM := VSM.
Module VSM := VSM.
Import VSM VeriStarLogic.

Module SPredLems := SPredLemmas VSM. Import SPredLems.
Module Clausify := Clausify_Sound VSM. Import Clausify.

Import sepalg.

Lemma spatial_resolution_sound:
  forall (nc pc c: clause) s,
  clause_denote nc s -> clause_denote pc s ->
  spatial_resolution nc pc = M.singleton c ->
  clause_denote c s.
Proof.
intros.
destruct nc; simpl in *.
 contradiction (empty_not_singleton _ H1).
destruct pc. simpl in *.
 contradiction (empty_not_singleton _ H1).
 contradiction (empty_not_singleton _ H1).
2:  contradiction (empty_not_singleton _ H1).
remember (eq_space_atomlist (rsort compare_space_atom sigma0)
           (rsort compare_space_atom sigma)) as b; destruct b; inversion H1.
apply singleton_inv in H3. subst c.
clear H1.
simpl.
  assert (X:= eq_space_atomlist_sound _ _ Heqb). clear Heqb.
  unfold clause_denote. intros. simpl.
  rewrite <- list_denote_union_normalize_pure_atoms.
  rewrite list_denote_normalize_filter_nonreflex_atom in H1.
  destruct (list_denote_inter_app _ _ _ _ H1) as [HL HL0]. clear H1.
  assert (K0 := H HL0). clear H HL0.
   rewrite (list_denote_assoc_sym_id pure_atom_denote (@orp state) (space_denote sigma) FF delta) in K0.
   destruct K0.
   (*Case1*)
     apply list_denote_union_left.
     apply H0.
     rewrite (@listd_unfold_inter _ state). split. apply HL.

     unfold space_denote in *.
     destruct (list_denote_sepcon_sort space_atom_denote emp sigma compare_space_atom s) as [X1 _].
     destruct (list_denote_sepcon_sort space_atom_denote emp sigma0 compare_space_atom s) as [_ X2].
     apply X2. clear X2. rewrite X. clear X. apply X1. apply H.
    (*Case 2*)
     apply list_denote_union_right. apply H.

  apply spred.orpN.
  apply spred.orpS.
  apply spred.orpA.
 contradiction (empty_not_singleton _ H3).
Qed.

Lemma sr_sound c1 c2 (b: spred) s :
  clause_denote c1 s -> clause_denote c2 s -> b s ->
  setd clause_denote inter b (spatial_resolution c1 c2) s.
Proof with simpl; auto; try solve[congruence].
intros H1 H2 H3.
remember (spatial_resolution c1 c2) as l.
case_eq (M.is_empty l); intros.
rewrite M.is_empty_spec in H.
rewrite (@setd_base_separate state); auto.
split; auto.
unfold setd.
rewrite empty_set_elems' in H. rewrite H. simpl; auto.
assert (exists c, l = M.singleton c).
subst l.
rewrite is_empty_spec' in H.
clear - H.
destruct c1; simpl in *; try (contradiction H; apply M.empty_spec).
destruct c2; simpl in *; try (contradiction H; apply M.empty_spec).
if_tac in H;simpl in *; try (contradiction H; apply M.empty_spec).
econstructor; eauto.
destruct H0 as [c ?].
subst l.
rewrite H0.
clear H.
eapply spatial_resolution_sound in H0; eauto.
unfold setd.
rewrite elements_singleton; simpl; split; auto.
Qed.

Definition Rule_U1 (nc pc : clause) :=
 match nc , pc with
   PosSpaceClause Gamma Delta ((Next x z)::Sigma) ,
   NegSpaceClause Gamma' (Lseg x' z'::Sigma') Delta' =>
     match expr_cmp x x', expr_cmp z z' with
      Eq, Eq => Some (NegSpaceClause Gamma' (Next x' z'::Sigma')
                        (Eqv x z :: Delta'))
     | _, _ => None
     end
  | _ , _ => None
 end.

(*The axiom schema for U1 from Figure 2, used as an auxiliary lemma for the proof of U1*)
Lemma U1_axiomSchema: forall x z Sigma s,
  space_denote (Next x z::Sigma) s ->
  pure_atom_denote (Eqv x z) s \/ space_denote (Lseg x z::Sigma) s.
Proof. simpl.
intros.
destruct H as [s1 [s2 [J [S1 S2]]]]. fold @list_denote in S2.
simpl in S1.
 revert S1; case_eq ( val2loc (expr_denote x s1)); intros; try contradiction. destruct S1.
unfold var_eq.
assert (Decidable.decidable (expr_denote x s = expr_denote z s)).
 apply expr_denote_eq_dec_loc; auto.
 replace (expr_denote x s) with (expr_denote x s1); [right; eauto | ].
 clear - J; destruct s; destruct s1; destruct J as [[? ?] ?]; simpl in *; subst.
  apply expr_denote_heap_ind; auto.
destruct H2; auto; right.
 exists s1. exists s2. split. assumption. split. simpl.
     destruct (join_ex_units (hp s1)) as [eh ?].
     eapply lseg_cons.  contradict H2.
      eapply state_join_var_eq; eauto.
      eassumption. eassumption.
      constructor 1. eapply unit_identity; apply u. auto.
      auto.
      auto.
Qed.

Lemma U1_sound: forall nc pc c s,
  clause_denote nc s -> clause_denote pc s ->
  Rule_U1 nc pc = Some c ->
  clause_denote c s.
Proof.
intros.
destruct nc; simpl in *. inversion H1. Focus 2. inversion H1.
destruct sigma. inversion H1.
destruct s0. Focus 2. inversion H1.
destruct pc. inversion H1. inversion H1.
destruct sigma0. inversion H1.
destruct s0. inversion H1.
case_eq (expr_cmp e e1); intros; rewrite H2 in H1.
 Focus 2. inversion H1. Focus 2. inversion H1.
case_eq (expr_cmp e0 e2); intros; rewrite H3 in H1; inversion H1; clear H1.
simpl in *. intros. clear H5 c.
rewrite  (@listd_unfold_inter _ state) in H1. destruct H1.
destruct (U1_axiomSchema _ _ _ _ H4); clear H4.
  left. simpl in H5.
  assert (X1:= expr_cmp_eq' _ _ s H2).
  assert (X2:= expr_cmp_eq' _ _ s H3).
  eapply var_eq_trans. apply X1. eapply var_eq_trans. apply H5. eapply var_eq_sym. apply X2.
right; clear H.
  apply H0. rewrite  (@listd_unfold_inter _ state).
  split; assumption.
Qed.

Lemma U1_sound': forall nc pc c s,
  clause_denote pc s ->
  Rule_U1 nc pc = Some c ->
  clause_denote c s.
Proof.
intros.
destruct nc; simpl in *. inversion H0. Focus 2. inversion H0.
destruct sigma. inversion H0.
destruct s0. Focus 2. inversion H0.
destruct pc. inversion H0. inversion H0.
destruct sigma0. inversion H0.
destruct s0. inversion H0.
case_eq (expr_cmp e e1); intros; rewrite H1 in H0.
 Focus 2. inversion H0. Focus 2. inversion H0.
case_eq (expr_cmp e0 e2); intros; rewrite H2 in H0; inversion H0; clear H0.
simpl in *. intros. clear H4 c.
rewrite  (@listd_unfold_inter _ state) in H0. destruct H0.
destruct (U1_axiomSchema _ _ _ _ H3); clear H3.
  left. simpl in H4.
  assert (X1:= expr_cmp_eq' _ _ s H1).
  assert (X2:= expr_cmp_eq' _ _ s H2).
  eapply var_eq_trans. apply X1. eapply var_eq_trans. apply H4. eapply var_eq_sym. apply X2.
right; clear H2.
  apply H. rewrite  (@listd_unfold_inter _ state).
  split; assumption.
Qed.

(*Lemma SR: forall pc nc ,
(forall s, clause_denote pc s /\ clause_denote nc s) ->
forall s, setd clause_denote inter TT (spatial_resolution pc nc) s.
Proof.
intros.
assert (SE: setd clause_denote inter TT M.empty s).
unfold setd. rewrite empty_set_elems. split;  auto.
destruct pc; simpl; trivial.
destruct nc; simpl; trivial.
remember (eq_space_atomlist (rsort compare_space_atom sigma0)
        (rsort compare_space_atom sigma)) as b.
destruct b; simpl; trivial. simpl in H.
unfold setd. rewrite elements_singleton. simpl.
split; trivial; simpl.
  intros.
  rewrite (list_denote_normalize_filter_nonreflex_atom TT) in H0.
  rewrite (@listd_unfold_app_inter _ state) in H0. destruct H0.
  destruct (H s). clear H.
  assert (HH1 := H2 H1). clear H2 H1.
  rewrite <- list_denote_union_normalize_pure_atoms.
rewrite (@listd_unfold_app_un _ state).
rewrite (@listd_unfold_un _ state) in HH1.
  destruct HH1.
   right. assumption.
  left. apply H3.  clear H3.
rewrite (@listd_unfold_inter _ state).
  split. apply H0.
  assert (KK:= eq_space_atomlist_sound _ _ Heqb). clear Heqb.
  unfold space_denote in *. rewrite listd_sort in KK. rewrite listd_sort in KK.
   rewrite KK. assumption.
  apply sepcon_comm. apply sepconA.
  apply sepcon_comm. apply sepconA.
Qed.
*)

Lemma unfolding1'_sound: forall  sigma2 sigma0 sigma1 p sig2' s,
  In (p,sig2') (unfolding1' sigma0 sigma1 sigma2) ->
  space_denote sig2' s ->
  (pure_atom_denote p s \/ space_denote (sigma0++sigma2) s).
Proof.
intros sigma2.
induction sigma2; simpl; intros; subst; simpl in *.
  contradiction.
rewrite <- (space_denote_permute _ _ (Permutation_middle sigma0 sigma2 a)).
destruct a.
  apply (IHsigma2 _ _ _ _ _ H H0).
destruct e.
  apply (IHsigma2 _ _ _ _ _ H H0).
remember (next_in_dom1 v e0 sigma1) as b.
destruct b; subst; simpl in *.
  apply eq_sym in Heqb.
  destruct H. inversion H; subst. clear H IHsigma2.
    rewrite space_insert in H0.
    destruct (U1_axiomSchema _ _ _ _ H0); clear H0.
    left. assumption.
    right. assert (Permutation (Lseg (Var v) e0 :: (rev sigma0 ++ sigma2)) (Lseg (Var v) e0 :: sigma0 ++ sigma2)).
            apply perm_skip. apply Permutation_app_tail. apply Permutation_sym. apply Permutation_rev.
           rewrite (space_denote_permute _ _ H0) in H. apply H.
  apply (IHsigma2 _ _ _ _ _ H H0).
apply (IHsigma2 _ _ _ _ _ H H0).
Qed.

Lemma unfolding1_sound: forall sc1 sc2,
  forall s, clause_denote sc2 s ->
  listd clause_denote inter TT (unfolding1 sc1 sc2) s.
Proof.
intros.
destruct sc1; simpl; trivial.
destruct sc2; simpl; trivial.
rewrite (@listd_unfold_inter _ state).
eapply listd_inter_map.
  intros.
  simpl in H. destruct x as [p sig2'].
  simpl. intros.
  rewrite (@listd_unfold_inter _ state) in H1.
  destruct H1.
    rewrite (@listd_unfold_un _ state).
    left.
    rewrite listd_insert_uniq.
    destruct (unfolding1'_sound _ _ _ _ _ _ H0 H2).
      left. rewrite <- pure_atom_denote_order_eqv_pure_atom. apply H3.
      right. apply H. simpl in H3.
        rewrite (@listd_unfold_inter _ state).
        split; assumption.
    apply union_com.
    intros. rewrite union_assoc. trivial.
    intros. do_comp pure_atom_cspec x y; try congruence.
    subst x. apply unXX.
Qed.

Definition Rule_U2 (nc pc : clause) :=
 match nc , pc with
   PosSpaceClause Gamma Delta ((Next x y)::Sigma) ,
   NegSpaceClause Gamma' (Lseg x' z::Sigma') Delta' =>
     match expr_cmp x x' with
      Eq => Some (NegSpaceClause Gamma' (Next x y::Lseg y z::Sigma')
                   (Eqv x z :: Delta'))
     |_ => None
     end
  | _ , _ => None
 end.

(*The axiom schema for U2 from Figure 2, used as an auxiliary lemma for the proof of U2*)
Lemma U2_axiomSchema: forall x y z Sigma s,
  space_denote (Next x y::Lseg y z::Sigma) s ->
  pure_atom_denote (Eqv x z) s \/ space_denote (Lseg x z::Sigma) s.
Proof.
intros.
unfold space_denote in H.
rewrite listd_cons in H.
destruct H as [s1 [s2 [J [S1 S2]]]].
simpl in S1.
revert S1; case_eq (val2loc (expr_denote x s1)); intros; try contradiction.
destruct S1 as [HP1 F2 (* [HP2] *) ].
rewrite listd_cons in S2.
destruct S2 as [s21 [s22 [J1 [S21 S22]]]].
simpl in S21.
destruct (expr_denote_eq_dec_loc x z s). right; exists l.
replace (expr_denote x s) with (expr_denote x s1); auto.
clear - J; destruct s1; destruct s2; destruct s; destruct J as [[? ?] ?]; simpl in *; subst.
apply expr_denote_heap_ind; auto.
  left. apply H0.
  right.
  unfold space_denote. rewrite listd_cons.
  destruct (join_assoc (join_comm J1) (join_comm J)) as [t [Jt1 Jt2]].
  exists t. exists s22. split. apply (join_comm Jt2).
  split; [ | assumption].
  simpl.
  destruct s1, s, s2, s21, s22, t;
  destruct Jt1 as [[? ?] ?]; destruct Jt2 as [[? ?] ?]; destruct J as [[? ?] ?]; destruct J1 as [[? ?] ?];
  simpl in *; subst. clear H5 H1 H4.
  eapply lseg_cons. contradict H0; apply H0.
  rewrite expr_denote_heap_ind with (h':=h4) in H; apply H.
  eauto.
  apply S21. simpl. auto.
Qed.

Lemma U2_sound: forall nc pc c s,
  clause_denote nc s -> clause_denote pc s ->
  Rule_U2 nc pc = Some c ->
  clause_denote c s.
Proof.
intros.
destruct nc; simpl in *. inversion H1. Focus 2. inversion H1.
destruct sigma. inversion H1.
destruct s0. Focus 2. inversion H1.
destruct pc. inversion H1. inversion H1.
destruct sigma0. inversion H1.
destruct s0. inversion H1.
case_eq (expr_cmp e e1); intros; rewrite H2 in H1.
 Focus 2. inversion H1. Focus 2. inversion H1.
  inversion H1; clear H1.
simpl. intros. clear H4 c.
rewrite  (@listd_unfold_inter _ state) in H1. destruct H1.
destruct (U2_axiomSchema _ _ _ _ _ H3); clear H3.
  left. apply H4.
right. clear H.
  apply H0. rewrite (@listd_unfold_inter _ state).
  split. assumption.
  unfold space_denote. rewrite listd_cons.
   unfold space_denote in H4.
   eapply sepcon_derives. Focus 3. apply H4.
     intros ss Hss. rewrite <- (var_eq_Lseg e e1 e2). apply Hss.
      apply (expr_cmp_eq' _ _ _ H2). apply var_eq_refl.
   trivial.
Qed.

Lemma U2_sound': forall nc pc c s,
  clause_denote pc s ->
  Rule_U2 nc pc = Some c ->
  clause_denote c s.
Proof.
intros.
destruct nc; simpl in *. inversion H0. Focus 2. inversion H0.
destruct sigma. inversion H0.
destruct s0. Focus 2. inversion H0.
destruct pc. inversion H0. inversion H0.
destruct sigma0. inversion H0.
destruct s0. inversion H0.
case_eq (expr_cmp e e1); intros; rewrite H1 in H0; inversion H0.
simpl; intros. clear H3 H0 c.
rewrite (@listd_unfold_inter _ state) in H2. destruct H2.
destruct (U2_axiomSchema _ _ _ _ _ H2); clear H2.
  left. apply H3.
right.
  apply H. rewrite (@listd_unfold_inter _ state).
  split. assumption.
  unfold space_denote. rewrite listd_cons.
   unfold space_denote in H3.
   eapply sepcon_derives. Focus 3. apply H3.
     intros ss Hss. rewrite <- (var_eq_Lseg e e1 e2). apply Hss.
      apply (expr_cmp_eq' _ _ _ H1). apply var_eq_refl.
   trivial.
Qed.

Lemma unfolding2'_sound: forall  sigma2 sigma0 sigma1 p sig2' s,
  In (p,sig2') (unfolding2' sigma0 sigma1 sigma2) ->
  space_denote sig2' s ->
  (pure_atom_denote p s \/ space_denote (sigma0++sigma2) s).
Proof.
intros sigma2.
induction sigma2; simpl; intros; subst; simpl in *.
  contradiction.
rewrite <- (space_denote_permute _ _ (Permutation_middle sigma0 sigma2 a)).
destruct a.
  apply (IHsigma2 _ _ _ _ _ H H0).
destruct e.
  apply (IHsigma2 _ _ _ _ _ H H0).
remember (next_in_dom2 v e0 sigma1) as b.
destruct b; subst; simpl in *.
  apply eq_sym in Heqb.
  destruct H. inversion H; subst. clear H IHsigma2.
    rewrite space_insert in H0.
    assert (P: Permutation (Next (Var v) e
        :: insert (rev_cmp compare_space_atom)
             (Lseg e e0) (rev sigma0 ++ sigma2))
          (Next (Var v) e
        :: (Lseg e e0) :: (rev sigma0 ++ sigma2))).
       apply perm_skip. apply perm_insert.
    rewrite (space_denote_permute _ _ P) in H0. clear P.
    destruct (U2_axiomSchema _ _ _ _ _ H0); clear H0.
    left. assumption.
    right. assert (Permutation (Lseg (Var v) e0 :: (rev sigma0 ++ sigma2)) (Lseg (Var v) e0 :: sigma0 ++ sigma2)).
            apply perm_skip. apply Permutation_app_tail. apply Permutation_sym. apply Permutation_rev.
           rewrite (space_denote_permute _ _ H0) in H. apply H.
  apply (IHsigma2 _ _ _ _ _ H H0).
apply (IHsigma2 _ _ _ _ _ H H0).
Qed.

Lemma unfolding2_sound: forall sc1 sc2,
  forall s, clause_denote sc2 s ->
  listd clause_denote inter TT (unfolding2 sc1 sc2) s.
Proof.
intros.
destruct sc1; simpl; trivial.
destruct sc2; simpl; trivial.
rewrite (@listd_unfold_inter _ state).
eapply listd_inter_map.
  intros.
  simpl in H. destruct x as [p sig2'].
  simpl. intros.
  rewrite (@listd_unfold_inter _ state) in H1.
  destruct H1.
    rewrite (@listd_unfold_un _ state).
    left.
    rewrite listd_insert_uniq.
    destruct (unfolding2'_sound _ _ _ _ _ _ H0 H2).
      left. rewrite <- pure_atom_denote_order_eqv_pure_atom. apply H3.
      right. apply H. simpl in H3.
        rewrite (@listd_unfold_inter _ state).
        split; assumption.
    apply union_com.
    intros. rewrite union_assoc. trivial.
    intros. do_comp pure_atom_cspec x y; try congruence.
    subst x. apply unXX.
Qed.

Definition Rule_U3 (nc pc : clause) :=
 match nc , pc with
   PosSpaceClause Gamma Delta ((Lseg x y)::Sigma) ,
   NegSpaceClause Gamma' (Lseg x' Nil::Sigma') Delta' =>
     match expr_cmp x x' with
      Eq => Some (NegSpaceClause Gamma' (Lseg x y::Lseg y Nil::Sigma') Delta')
     |_ => None
     end
  | _ , _ => None
 end.

(*The axiom schema for U3 from Figure 2, used as an auxiliary lemma for the proof of U3*)
Lemma U3_axiomSchema: forall x y Sigma s,
  space_denote (Lseg x y::Lseg y Nil::Sigma) s ->
  space_denote (Lseg x Nil::Sigma) s.
Proof.
intros.
unfold space_denote in H.
rewrite listd_cons in H.
rewrite listd_cons in H.
destruct H as [s1 [s2 [J1 [S1 [s21 [s22 [J2 [S21 S22]]]]]]]].
simpl in S1. simpl in S21.
destruct (join_assoc (join_comm J2) (join_comm J1)) as [t [Jt1 Jt2]].
  exists t. exists s22. split. apply (join_comm Jt2).
  split. simpl.
  clear - S1 S21 Jt1.
  destruct s1,s21,t; destruct Jt1 as [[? ?] Jt1]; simpl in *; subst.
  apply (lseg_appN _ _ _ _ _ S1 S21 (join_comm Jt1)).
  assumption.
Qed.

Lemma U3_sound: forall nc pc c s,
  clause_denote nc s -> clause_denote pc s ->
  Rule_U3 nc pc = Some c ->
  clause_denote c s.
Proof.
intros.
destruct nc; simpl in *. inversion H1. Focus 2. inversion H1.
clear H.
destruct sigma. inversion H1.
destruct s0. inversion H1.
destruct pc. inversion H1. inversion H1.
destruct sigma0. inversion H1.
destruct s0. inversion H1.
destruct e2. Focus 2. inversion H1.
case_eq (expr_cmp e e1); intros; rewrite H in H1; inversion H1. clear H1.
simpl in *. intros. clear H3 c.
rewrite (@listd_unfold_inter _ state) in H1. destruct H1.
apply H0.
rewrite (@listd_unfold_inter _ state).
split. assumption.
apply U3_axiomSchema with (y:=e0).
clear H0 H1.
unfold space_denote in *.
rewrite listd_cons in *.
eapply sepcon_derives. Focus 3. apply H2.
  intros w Hw. rewrite <- (var_eq_Lseg1 e e1 e0). apply Hw.
    apply (expr_cmp_eq' _ _ _ H).
  trivial.
Qed.

Lemma U3_sound': forall nc pc c s,
  clause_denote pc s ->
  Rule_U3 nc pc = Some c ->
  clause_denote c s.
Proof.
intros.
destruct nc; simpl in *. inversion H0. Focus 2. inversion H0.
destruct sigma. inversion H0.
destruct s0. inversion H0.
destruct pc. inversion H0. inversion H0.
destruct sigma0. inversion H0.
destruct s0. inversion H0.
destruct e2. Focus 2. inversion H0.
case_eq (expr_cmp e e1); intros; rewrite H1 in H0; inversion H0. clear H0.
(*rewrite H1 in H3. clear H3.*)
simpl in *. intros. clear H3 c.
rewrite (@listd_unfold_inter _ state) in H0. destruct H0.
apply H.
rewrite (@listd_unfold_inter _ state).
split. assumption.
apply U3_axiomSchema with (y:=e0).
clear H0 H.
unfold space_denote in *.
rewrite listd_cons in *.
eapply sepcon_derives. Focus 3. apply H2.
  intros w Hw. rewrite <- (var_eq_Lseg1 e e1 e0). apply Hw.
    apply (expr_cmp_eq' _ _ _ H1).
  trivial.
Qed.

Lemma unfolding3'_sound: forall  sigma2 sigma0 sigma1 sig2' s,
  In sig2' (unfolding3' sigma0 sigma1 sigma2) ->
  space_denote sig2' s -> space_denote (sigma0++sigma2) s.
Proof.
intros sigma2.
induction sigma2; simpl; intros; subst; simpl in *.
  contradiction.
rewrite <- (space_denote_permute _ _ (Permutation_middle sigma0 sigma2 a)).
destruct a.
  apply (IHsigma2 _ _ _ _ H H0).
destruct e.
  apply (IHsigma2 _ _ _ _ H H0).
destruct e0.
  remember (lseg_in_dom2 v Nil sigma1 ) as b.
  destruct b; subst; simpl in *.
    apply eq_sym in Heqb.
    destruct H. subst. clear IHsigma2.
      rewrite space_insert in H0.
      assert (P: Permutation (Lseg (Var v) e
        :: insert (rev_cmp compare_space_atom)
             (Lseg e Nil) (rev sigma0 ++ sigma2))
          (Lseg (Var v) e
        :: (Lseg e Nil) :: (rev sigma0 ++ sigma2))).
        apply perm_skip. apply perm_insert.
      rewrite (space_denote_permute _ _ P) in H0. clear P.
      assert (SS:= U3_axiomSchema _ _ _ _ H0); clear H0.
      assert (Permutation (Lseg (Var v) Nil :: (rev sigma0 ++ sigma2)) (Lseg (Var v) Nil :: sigma0 ++ sigma2)).
            apply perm_skip. apply Permutation_app_tail. apply Permutation_sym. apply Permutation_rev.
           rewrite (space_denote_permute _ _ H) in SS. apply SS.
    apply (IHsigma2 _ _ _ _ H H0).
  apply (IHsigma2 _ _ _ _ H H0).
apply (IHsigma2 _ _ _ _ H H0).
Qed.

Lemma unfolding3_sound: forall sc1 sc2,
  forall s, clause_denote sc2 s
  -> listd clause_denote inter TT (unfolding3 sc1 sc2) s.
Proof.
intros.
destruct sc1; simpl; trivial.
destruct sc2; simpl; trivial.
rewrite (@listd_unfold_inter _ state).
eapply listd_inter_map.
  intros.
  simpl in H.
  simpl. intros.
  rewrite (@listd_unfold_inter _ state) in H1.
  destruct H1.
    rewrite (@listd_unfold_un _ state).
    left.
    apply H.
    rewrite (@listd_unfold_inter _ state).
    split. assumption.
    apply (unfolding3'_sound _ _ _ _ _ H0 H2).
Qed.

Lemma lseg_prefix: forall x y z l h,
    lseg x y h ->
    val2loc z = Some l ->
    ~emp_at l h ->
 exists h' : heap, lseg x z h' /\
                   join_sub h' h /\ emp_at l h'.
Proof.
intros.
revert l z H0 H1; induction H; simpl; intros.
 contradict H2. apply heap_gempty; auto.
 rename x' into l'.
 rename z0 into u.
 destruct (classic (x=u)).
 subst.
 destruct (join_ex_units s) as [eh ?]. exists eh. split; [|split]; auto. constructor 1; auto.
 eapply unit_identity; eauto. right; eauto. econstructor; apply u0.  apply heap_gempty.
 eapply unit_identity; eauto.
 specialize (IHlseg _ _ H4).
 destruct IHlseg as [h' [? ?]].
 contradict H5.
 apply emp_at_join with l in H3; auto. apply H3; split; auto.
 eapply rawnext_out in H1; eauto. contradict H6; subst.  eapply val2loc_inj; eauto.
 destruct H8.
 destruct H8 as [h2 ?].
 destruct (join_assoc (join_comm H8) (join_comm H3)) as [hf [? ?]].
 exists hf; split; [|split];auto.
 econstructor 2; eauto. econstructor; eauto.
 apply emp_at_join with l in H10. apply H10; split; auto.
 eapply rawnext_out; eauto.
 contradict H6; subst; eapply val2loc_inj;  eauto.
Qed.

(*The axiom schema for U4 from Figure 2, used as an auxiliary lemma for the proof of U4*)
Lemma U4_axiomSchema: forall x y z w Sigma s,
  space_denote (Lseg x y::Lseg y z::Next z w::Sigma) s ->
  space_denote (Lseg x z::Next z w::Sigma) s.
Proof.
intros.
unfold space_denote in H.
rewrite listd_cons in H.
rewrite listd_cons in H.
destruct H as [st1 [st2 [J1 [S1 [st21 [st22 [J2 [S21 S22]]]]]]]].
simpl in S1. simpl in S21.
destruct (join_assoc (join_comm J2) (join_comm J1)) as [t [Jt1 Jt2]].
exists t. exists st22. split. apply (join_comm Jt2).
split; auto.
simpl.
  assert (Z: exists lz, val2loc (expr_denote z t) = Some lz /\ emp_at lz (hp t)).
    destruct S22 as [st221 [st222 [JJ [T1 T2]]]]. clear T2.
    revert T1; simpl. case_eq (val2loc (expr_denote z st221)); intros; try contradiction.
    rename l into lz. rename H into Z1; destruct T1 as [Z2 Z3].
     exists lz.
     split. replace (expr_denote z t) with (expr_denote z s).
              rewrite (expr_denote_join z _ _ _ Jt2).
              rewrite (expr_denote_join z _ _ _ JJ). apply Z1.
            apply (expr_denote_join z _ _ _ (join_comm Jt2)).
            destruct JJ as [_ JJ].
           destruct (rawnext_at1 (rawnext2rawnext' Z2) JJ).
           destruct Jt2 as [_ Jt2].
           destruct (rawnext_at1 H0 Jt2); auto.
  destruct Z as [tz [Tz Hz]]. clear S22.
  clear - S1 S21 Jt1 Tz Hz.
  destruct st21,st1,t; destruct Jt1 as [[? ?] Jt1]; simpl in *; subst.
    apply (lseg_lseg_app _ _ _ _ _ _ _ S1 S21 Jt1 Tz Hz).
Qed.

Lemma next_in_dom_app: forall v sigma sigma',
  true = next_in_dom v sigma -> true = next_in_dom v (sigma ++ sigma').
Proof.
unfold next_in_dom.
intros v sigma.
induction sigma; simpl; intros. inversion H.
destruct a; simpl.
  destruct e; simpl. apply IHsigma. apply H.
  remember (Ident.eq_dec v v0) as bb.
  destruct bb; simpl in *. trivial. apply IHsigma. apply H.
apply IHsigma. apply H.
Qed.

Lemma next_in_dom_true: forall v sigma s,
  true = next_in_dom v sigma ->
  space_denote sigma s ->
  exists w, exists sig, space_denote (Next (Var v) w::sig) s /\
    Permutation (Next (Var v) w::sig) sigma.
Proof.
intros v sigma.
induction sigma; simpl; intros. inversion H.
destruct a; simpl in *.
  destruct e; simpl in *.
    destruct H0 as [st1 [st2 [J1 [H1 H2]]]].
    rewrite VeriStarLogic.nil_not_loc in H1. contradiction.
  remember (Ident.eq_dec v v0) as b; destruct b; subst; simpl in *.
    clear H. exists e0. exists sigma.
    split. apply H0. apply Permutation_refl.
  destruct H0 as [st1 [st2 [J1 [H1 H2]]]].
    destruct (IHsigma _ H H2) as [w [sig [Hsig1 Hsig2]]]. clear IHsigma H H2.
    exists w. exists (Next (Var v0) e0 :: sig).
    destruct Hsig1 as [st3 [st4 [J2 [H3 H4]]]].
    split.
      exists st3.
      destruct (join_assoc J2 (join_comm J1)) as [stt [JJ1 JJ2]].
      exists stt. split. assumption.
       split. assumption.
       exists st1. exists st4. split. apply join_comm. assumption.
            split. apply H1. apply H4.
     eapply perm_trans. apply perm_swap. apply perm_skip. apply Hsig2.
  destruct H0 as [st1 [st2 [J1 [H1 H2]]]].
    destruct (IHsigma _ H H2) as [w [sig [Hsig1 Hsig2]]]. clear IHsigma H H2.
    exists w. exists (Lseg e e0 :: sig).
    destruct Hsig1 as [st3 [st4 [J2 [H3 H4]]]].
    split.
      exists st3.
      destruct (join_assoc J2 (join_comm J1)) as [stt [JJ1 JJ2]].
      exists stt. split. assumption.
        split. assumption.
        exists st1. exists st4. split. apply join_comm. assumption.
             split. apply H1. apply H4.
     eapply perm_trans. apply perm_swap. apply perm_skip. apply Hsig2.
Qed.

Lemma lseg_in_dom_app: forall sig p v sigma,
  In p (lseg_in_dom_atoms v sigma) -> In p (lseg_in_dom_atoms v (sig ++ sigma)).
Proof.
intros sig.
induction sig; simpl; intros. assumption.
destruct a; simpl in *. apply IHsig. assumption.
destruct e; simpl in *. apply IHsig. assumption.
remember (Ident.eq_dec v v0) as b; destruct b; subst; simpl in *.
  right. apply IHsig. assumption.
 apply IHsig. assumption.
Qed.

Lemma incl_nil: forall {A} (l:list A) , incl l [] -> l = [].
Proof.
intros A l.
induction l; intros; subst;  simpl in *. trivial.
unfold incl in H.
destruct (H a). left. trivial.
Qed.

Lemma incl_consD: forall {A} (a:A) sigma sig, incl (a :: sigma) sig ->
  In a sig /\ incl sigma sig.
Proof.
intros.
unfold incl in *.
split. apply H. left. trivial.
intros. apply H. right. apply H0.
Qed.

Lemma lseg_in_dom_app2: forall sig p v sigma,
  In p (lseg_in_dom_atoms v sigma) -> In p (lseg_in_dom_atoms v (sigma ++ sig)).
Proof.
intros.
induction sigma; simpl in *; intros. contradiction.
destruct a; simpl in *. apply IHsigma. assumption.
destruct e; simpl in *. apply IHsigma. assumption.
remember (Ident.eq_dec v v0) as b; destruct b; subst; simpl in *.
  destruct H. left. assumption.
  right. apply IHsigma. assumption.
 apply IHsigma. assumption.
Qed.

Lemma pure_atom_denote_join: forall p s1 s2 s,
  join s1 s2 s ->
  pure_atom_denote p s = pure_atom_denote p s1.
Proof.
intros.
destruct s. destruct s1.
assert (s0 = s).
  destruct H. destruct H. simpl in *. rewrite H. rewrite <- H1. trivial.
subst.
apply pure_atom_denote_heap_ind.
Qed.

Lemma lseg_in_dom_atoms_Space_denotePerm:
  forall sig p v s,
        (space_denote sig) s -> In p (lseg_in_dom_atoms v sig) ->
     pure_atom_denote p s \/ (exists sig1, exists y,
              space_denote (Lseg (Var v) y::sig1) s /\
              Permutation sig (Lseg (Var v) y :: sig1)).
Proof.
intros sig.
induction sig; simpl in *; intros. contradiction.
destruct a.
  destruct H as [s1 [s1' [J1 [K1 K1']]]].
  destruct (IHsig _ _ _ K1' H0).
    left. rewrite (pure_atom_denote_join p _ _ _ (join_comm J1)). assumption.
  destruct H as [sig1 [y [HH1 HH2]]].
    right. exists (Next e e0 :: sig1). exists y.
      split. rewrite Space_denote_cons. rewrite <- sepcon_assoc.
               rewrite <- (sepcon_comm (space_atom_denote (Next e e0))).
              rewrite sepcon_assoc.
              exists s1. exists s1'. split. assumption. split; assumption.
                eapply perm_trans. apply perm_skip. apply HH2. apply perm_swap.
destruct e.
  destruct H as [s1 [s1' [J1 [K1 K1']]]].
  destruct (IHsig _ _ _ K1' H0).
    left. rewrite (pure_atom_denote_join p _ _ _ (join_comm J1)). assumption.
  destruct H as [sig1 [y [HH1 HH2]]].
    right. exists (Lseg Nil e0 :: sig1). exists y.
      split. rewrite Space_denote_cons. rewrite <- sepcon_assoc.
               rewrite <- (sepcon_comm (space_atom_denote (Lseg Nil e0))).
              rewrite sepcon_assoc.
              exists s1. exists s1'. split. assumption. split; assumption.
                eapply perm_trans. apply perm_skip. apply HH2. apply perm_swap.
  destruct (Ident.eq_dec v v0); subst.
  destruct H0.
    remember (expr_cmp (Var v0) e0) as bb; destruct bb; subst; simpl in *.
       left. eapply expr_cmp_eq'. rewrite Heqbb. trivial.
       right. exists sig. exists e0.
              split. apply H. apply Permutation_refl.
       right. exists sig. exists e0.
              split. apply H. apply Permutation_refl.
  destruct H as [s1 [s1' [J1 [K1 K1']]]].
         destruct (IHsig _ _ _ K1' H0).
          left. rewrite (pure_atom_denote_join p _ _ _ (join_comm J1)). assumption.
       destruct H as [sig1 [y [HH1 HH2]]].
       right. exists (Lseg (Var v0) e0 :: sig1). exists y.
      split. rewrite Space_denote_cons. rewrite <- sepcon_assoc.
               rewrite <- (sepcon_comm (space_atom_denote (Lseg (Var v0) e0))).
              rewrite sepcon_assoc.
              exists s1. exists s1'. split. assumption. split; assumption.
                eapply perm_trans. apply perm_skip. apply HH2. apply perm_swap.
destruct H as [s1 [s1' [J1 [K1 K1']]]].
         destruct (IHsig _ _ _ K1' H0).
          left. rewrite (pure_atom_denote_join p _ _ _ (join_comm J1)). assumption.
       destruct H as [sig1 [y [HH1 HH2]]].
       right. exists (Lseg (Var v0) e0 :: sig1). exists y.
      split. rewrite Space_denote_cons. rewrite <- sepcon_assoc.
               rewrite <- (sepcon_comm (space_atom_denote (Lseg (Var v0) e0))).
              rewrite sepcon_assoc.
              exists s1. exists s1'. split. assumption. split; assumption.
                eapply perm_trans. apply perm_skip. apply HH2. apply perm_swap.
Qed.

Lemma lseg_in_dom_atoms_space_denote_perm_strong:
  forall sig p v s,
        (space_denote sig) s -> In p (lseg_in_dom_atoms v sig) ->
     exists y, (p=Eqv (Var v) y \/ p=Eqv y (Var v)) /\
           (pure_atom_denote p s \/
            exists sig1,
              space_denote (Lseg (Var v) y::sig1) s /\
              Permutation sig (Lseg (Var v) y :: sig1)).
Proof.
intros sig.
induction sig; simpl in *; intros. contradiction.
destruct a.
  destruct H as [s1 [s1' [J1 [K1 K1']]]].
  destruct (IHsig _ _ _ K1' H0).
    destruct H. exists x.
      split. trivial.
      destruct H1.
        left. rewrite (pure_atom_denote_join p _ _ _ (join_comm J1)). assumption.
        destruct H1 as [sig1 [HS1 HS2]]. right.
          exists (Next e e0 :: sig1).
          split. destruct HS1 as [t1 [t2 [JJ [T1 T2]]]].
                 exists t1. destruct (join_assoc JJ (join_comm J1)) as [u [U1 U2]].
                 exists u. split. trivial. split. apply T1.
                 exists s1. exists t2. split. apply join_comm. apply U1. split; assumption.
          eapply Permutation_trans. apply perm_skip. apply HS2. apply perm_swap.
destruct e.
  destruct H as [s1 [s1' [J1 [K1 K1']]]].
  destruct (IHsig _ _ _ K1' H0).
    destruct H. exists x.
      split. trivial.
      destruct H1.
        left. rewrite (pure_atom_denote_join p _ _ _ (join_comm J1)). assumption.
        destruct H1 as [sig1 [HS1 HS2]]. right.
          exists (Lseg Nil e0 :: sig1).
          split. destruct HS1 as [t1 [t2 [JJ [T1 T2]]]].
                 exists t1. destruct (join_assoc JJ (join_comm J1)) as [u [U1 U2]].
                 exists u. split. trivial. split. apply T1.
                 exists s1. exists t2. split. apply join_comm. apply U1. split; assumption.
          eapply Permutation_trans. apply perm_skip. apply HS2. apply perm_swap.
destruct (Ident.eq_dec v v0); subst.
  destruct H0. clear IHsig.
    remember (expr_cmp (Var v0) e0) as bb; destruct bb; subst; simpl in *.
    destruct e0. inversion Heqbb.
       apply comp_eq in Heqbb. subst. exists (Var v). split. left. trivial. left. apply var_eq_refl. unfold CompSpec'.
          assert (Ident.lt = (fun x y : Ident.t => Lt = Ident.compare x y)).
             apply extensionality. intros x.
             apply extensionality. intros y. generalize (Ident.compare_spec x y). intros. destruct H0.  subst. apply prop_ext.  split; try congruence. intros. exfalso. eapply Ilt_irrefl. apply H0.
             apply prop_ext; split; auto.
              apply prop_ext. split; intros. exfalso. eapply Ilt_irrefl. eapply Ilt_trans. apply H0. apply H1. inversion H1.
          rewrite <- H0. apply var_cspec.
    destruct e0. inversion Heqbb.
       exists (Var v). split. right. trivial. right. exists sig. split. apply H. apply Permutation_refl.
    destruct e0.
       exists Nil. split. left. trivial. right. exists sig. split. apply H. apply Permutation_refl.
     exists (Var v). split. left. trivial. right. exists sig. split. apply H. apply Permutation_refl.
  destruct H as [s1 [s2 [J [S1 S2]]]].
  assert (IH := IHsig p v0 _ S2 H0). clear IHsig H0.
    destruct IH as [y [Y1 Y2]].
       exists y. split; trivial.
       destruct Y2. left. rewrite (pure_atom_denote_join p _ _ _ (join_comm J)). assumption.
       destruct H as [sig1 [HS1 HS2]]. right.
          exists (Lseg (Var v0) e0 :: sig1).
          split. destruct HS1 as [t1 [t2 [JJ [T1 T2]]]].
                 exists t1. destruct (join_assoc JJ (join_comm J)) as [u [U1 U2]].
                 exists u. split. trivial. split. apply T1.
                 exists s1. exists t2. split. apply join_comm. apply U1. split; assumption.
          eapply Permutation_trans. apply perm_skip. apply HS2. apply perm_swap.
destruct H as [s1 [s1' [J1 [K1 K1']]]].
  destruct (IHsig _ _ _ K1' H0) as [y [Y1 Y2]].
  exists y. split; trivial.
  destruct Y2.
    left. rewrite (pure_atom_denote_join p _ _ _ (join_comm J1)). assumption.
  destruct H as [sig1 [HS1 HS2]].
    right.
          exists (Lseg (Var v0) e0 :: sig1).
          split. destruct HS1 as [t1 [t2 [JJ [T1 T2]]]].
                 exists t1. destruct (join_assoc JJ (join_comm J1)) as [u [U1 U2]].
                 exists u. split. trivial. split. apply T1.
                 exists s1. exists t2. split. apply join_comm. apply U1. split; assumption.
          eapply Permutation_trans. apply perm_skip. apply HS2. apply perm_swap.
Qed.

Lemma app_app: forall {A} (a:A) l ll l1 l2,
  l ++ ll = l1 ++ a :: l2 ->
  exists m, exists n,
    (l = l1 ++ a :: n /\ l2 = n ++ ll) \/
    (ll = m ++ a :: l2 /\ l1=l ++ m).
Proof.
intros A a l.
induction l; intros; simpl in *; subst; simpl.
  exists l1. exists l2. right. split; trivial.
destruct l1; simpl in *; inversion H; subst; clear H.
  exists nil. exists l. left. split; trivial.
destruct (IHl _ _ _ H2) as [M [N [[X1 X2]|[Y1 Y2]]]]; subst; clear IHl H2.
  exists nil. exists N. left. split; trivial.
exists M. exists nil. right. split; trivial.
Qed.

Lemma Perm_aux1: forall {A} (a:A) l0 l1 l2,
  Permutation l0 (l1 ++ a :: l2) ->
  exists l3 : list A,
    exists l4 : list A, l0 = l3 ++ a :: l4.
Proof.
intros.
remember (l1 ++ a :: l2) as al.
generalize dependent l2.
generalize dependent a.
generalize dependent l1.
induction H; intros; subst.
  destruct l1; simpl in *; inversion Heqal.
  destruct l1; simpl in *; inversion Heqal; subst; clear Heqal.
    exists nil. exists l. reflexivity.
    destruct (IHPermutation _ _ _ (eq_refl _)) as [l5 [l6 PP]]. subst.
      exists (a0::l5). exists l6. reflexivity.
  destruct l1; simpl in *; inversion Heqal; subst; clear Heqal.
    exists [y]. exists l. reflexivity.
  destruct l1; simpl in *; inversion H1; subst.
    exists nil. exists (a0::l2). reflexivity.
    exists (a1::a0::l1). exists l2. reflexivity.
destruct (IHPermutation2 _ _ _ (eq_refl _)) as [l5 [l6 IH2]]; subst; clear IHPermutation2.
  destruct (IHPermutation1 _ _ _ (eq_refl _)) as [l3 [l4 IH1]]; subst; clear IHPermutation1.
  exists l3. exists l4. reflexivity.
Qed.

Lemma Perm_aux: forall {A} (a a':A) l l',
  Permutation (a::l) (a'::l') ->
  (a=a' /\ Permutation l l') \/
  exists l1, exists l2, l = l1 ++ a'::l2 /\ Permutation (a::l1++l2) l'.
Proof.
intros.
remember (a'::l') as al'. generalize dependent l'. generalize dependent a'.
remember (a::l) as al. generalize dependent l. generalize dependent a.
induction H; intros; subst; simpl in *; try inversion Heqal.
  subst. clear Heqal. inversion Heqal'; subst; clear Heqal'.
  left. split; trivial.
subst. clear Heqal. inversion Heqal'; subst; clear Heqal'.
  right.  exists nil. exists l. simpl. split. trivial. apply Permutation_refl.
destruct l'. apply Permutation_length in H0. inversion H0.
  destruct (IHPermutation2 _ _ (eq_refl _) _ _ (eq_refl _)); clear IHPermutation2.
    destruct H1; subst.
    destruct (IHPermutation1 _ _ (eq_refl _) _ _ (eq_refl _)); clear IHPermutation1.
    destruct H1; subst. left. split. trivial. eapply Permutation_trans. apply H3. apply H2.
    destruct H1 as [l1 [l2 [L P]]]. subst.
      right. exists l1. exists l2. split. trivial. eapply Permutation_trans. apply P. apply H2.
destruct H1 as [l1 [l2 [L P]]]. subst.
  assert (Permutation l'0 (nil ++ (a0 :: (l1 ++ l2)))). apply Permutation_sym. apply P.
  destruct (Perm_aux1 _ _ _ _ H1) as [l3 [l4 X]]; subst. simpl in *.
  destruct (IHPermutation1 _ _ (eq_refl _) _ _ (eq_refl _)); clear IHPermutation1.
    destruct H2; subst.
      right. destruct (Perm_aux1 _ _ _ _ H3) as [l33 [l44 PP]].
        exists l33. exists l44. split. trivial.
        subst.
        assert (Permutation (l33 ++ l44) (l1 ++ l2)).
          eapply Permutation_cons_inv with (a:=a').
          eapply Permutation_trans. eapply Permutation_middle.
          eapply Permutation_trans. apply H3.
          apply Permutation_sym. apply Permutation_middle.
        eapply Permutation_trans. apply perm_skip. apply H2. apply P.
  destruct H2 as [l33 [l44 [L PP]]]. subst. clear H. clear H0.
   destruct (Perm_aux1 _ _ _ _ PP) as [x [y Z]]. rewrite Z in *.
   destruct x; simpl in *. inversion Z; subst. left. split. trivial.
      clear Z P. assert (Permutation (l33 ++ l44) (l1 ++ l2)).
                       eapply Permutation_cons_inv with (a:=a').
                       eapply Permutation_trans. apply PP. apply Permutation_sym. apply Permutation_middle.
          eapply Permutation_trans.  apply Permutation_sym. apply Permutation_middle.
          eapply Permutation_trans.  apply perm_skip. apply H. apply Permutation_sym. apply H1.
   apply eq_sym in Z. inversion Z. subst. rewrite Z in *. clear Z.
   right. apply eq_sym in H2.
   destruct (app_app _ _ _ _ _ H2) as [M [N [[X1 X2] | [Y1 Y2]]]]; subst; clear H2.
     exists x. exists (N++a0::l44). split. rewrite <- app_assoc. simpl. reflexivity.
       assert (Permutation (l1 ++ l2) (l3 ++ l4)).
         eapply Permutation_cons_inv with (a:=a0).
         eapply Permutation_trans. apply P. apply Permutation_sym. apply Permutation_middle.
       assert (Permutation (a::x ++ N ++ l44) (l1++l2)).
         eapply Permutation_cons_inv with (a:=a').
         eapply Permutation_trans. apply perm_swap.
         apply Permutation_trans with (l':=a :: (x ++ a' :: N) ++ l44).
            apply perm_skip. repeat rewrite app_assoc.
              assert ((x ++ a' :: N) ++ l44 = x ++ a' :: (N ++ l44)). rewrite <- app_assoc. simpl. trivial.
              rewrite H0.
              eapply Permutation_trans. apply (Permutation_middle (x++N) l44 a').
              assert ((x ++ N) ++ a' :: l44 = x ++ (N ++ a' :: l44)). rewrite app_assoc. trivial.
              rewrite H2. apply Permutation_app.  apply Permutation_refl.
              apply Permutation_sym.   apply Permutation_middle.
            eapply Permutation_trans. apply PP. clear PP. apply Permutation_sym. apply Permutation_middle.
          clear PP. assert (Permutation (a0::(l1++l2)) (l3++a0::l4)).
                      eapply Permutation_trans. apply perm_skip. apply H. apply Permutation_middle.
                 apply Permutation_trans with (l':=a0 :: l1 ++ l2).
                     clear H2. assert (Permutation (a :: x ++ N ++ a0 :: l44) (a0::(a :: x ++ N ++ l44))).
                             apply Permutation_sym. eapply Permutation_trans. apply perm_swap. apply perm_skip.
                             assert (x ++ N ++ a0 :: l44 = (x ++ N) ++ a0 :: l44). rewrite app_assoc. reflexivity. rewrite H2.
                                  assert (a0 :: x ++ N ++ l44 = a0 :: (x ++ N) ++ l44). rewrite app_assoc. reflexivity. rewrite H3.
                                  apply Permutation_middle.
                         eapply Permutation_trans. apply H2. apply perm_skip. apply H0.
                      apply H2.
        assert (Permutation (a::l33 ++ M ++ y) (l1++l2)).
            eapply Permutation_cons_inv with (a:=a').
            assert (a :: l33 ++ M ++ a' :: y = (a :: l33 ++ M) ++ a' :: y). simpl. rewrite app_assoc. trivial. rewrite H in PP. clear H.
            assert (a'::a :: l33 ++ M ++ y = a'::((a ::l33 ++ M) ++ y)). simpl. rewrite app_assoc.  trivial. rewrite H. clear H.
            eapply Permutation_trans. apply Permutation_middle.
            eapply Permutation_trans. apply PP. clear PP. apply Permutation_sym. apply Permutation_middle.
         clear PP.
        assert (Permutation (l1++l2) (l3++l4)).
            eapply Permutation_cons_inv with (a:=a0). eapply Permutation_trans. apply P. apply Permutation_sym. apply Permutation_middle.
          apply (Permutation_trans H) in H0. clear H.
            apply Permutation_cons with (a:=a0) in H0.
            exists (l33++a0::M). exists y. split. rewrite <- app_assoc. trivial.
            assert (Permutation (a :: a0::(l33 ++ M ++ y)) (l3++a0::l4)).
              eapply Permutation_trans. apply perm_swap.
              eapply Permutation_trans. apply H0. clear H0. apply Permutation_middle.
            clear H0.
            eapply Permutation_trans with (l':=a :: a0 :: l33 ++ M ++ y).
             apply perm_skip. apply Permutation_sym. clear H.
             eapply Permutation_trans. apply Permutation_middle. repeat  rewrite <- app_assoc. simpl. trivial.
          apply H.
Qed.

Lemma lseg_in_dom2Lemma: forall x y z sigma,
  Some y = lseg_in_dom2 x (Var z) sigma ->
  exists sigma2, Permutation sigma (Lseg (Var x) y :: sigma2).
Proof.
intros x y z sigma.
induction sigma; simpl; intros.
  inversion H.
destruct a. destruct (IHsigma H). exists (Next e e0 :: x0).
  eapply perm_trans. apply perm_skip. apply H0. apply perm_swap.
destruct e. destruct (IHsigma H). exists (Lseg Nil e0 :: x0).
  eapply perm_trans. apply perm_skip. apply H0. apply perm_swap.
remember (Ident.eq_dec x v) as b; destruct b; subst; simpl in *.
  remember (negb (expr_eq e0 (Var z))) as bb; destruct bb; subst; simpl in *.
    inversion H. subst.
    exists sigma. apply Permutation_refl.
  destruct (IHsigma H). exists (Lseg (Var v) e0 :: x).
    eapply perm_trans. apply perm_skip. apply H0. apply perm_swap.
destruct (IHsigma H). exists (Lseg (Var v) e0 :: x0).
    eapply perm_trans. apply perm_skip. apply H0. apply perm_swap.
Qed.

Lemma lseg_in_dom2Lemma_strong: forall x y z sigma,
  Some y = lseg_in_dom2 x (Var z) sigma ->
  exists sigma2, Permutation sigma (Lseg (Var x) y :: sigma2) /\
    (expr_eq y (Var z) =false).
Proof.
intros x y z sigma.
induction sigma; simpl; intros.
  inversion H.
destruct a. destruct (IHsigma H) as [sig [HS1 HS2]]. exists (Next e e0 :: sig).
  split. eapply perm_trans. apply perm_skip. apply HS1. apply perm_swap.
  assumption.
destruct e. destruct (IHsigma H) as [sig [HS1 HS2]]. exists (Lseg Nil e0 :: sig).
  split. eapply perm_trans. apply perm_skip. apply HS1. apply perm_swap.
  assumption.
remember (Ident.eq_dec x v) as b; destruct b; subst; simpl in *.
  remember (negb (expr_eq e0 (Var z))) as bb; destruct bb; subst; simpl in *.
    inversion H. subst.
    exists sigma. split. apply Permutation_refl.
    apply Bool.negb_sym in Heqbb.
       apply Heqbb.
  destruct (IHsigma H) as [sig [HS1 HS2]]. exists (Lseg (Var v) e0 :: sig).
    split. eapply perm_trans. apply perm_skip. apply HS1. apply perm_swap.
    assumption.
destruct (IHsigma H) as [sig [HS1 HS2]]. exists (Lseg (Var v) e0 :: sig).
  split. eapply perm_trans. apply perm_skip. apply HS1. apply perm_swap.
  assumption.
Qed.

Lemma lseg_unique: forall x y s
  (L:lseg x y s) s' (L': lseg x y s')
  t r (J: join s t r) t' (J': join s' t' r),
  s'=s /\ t'=t.
Proof.
intros x y s L.
induction L; intros; subst; simpl in *.
  assert (X:= join_unit1_e _ _ H J). subst.
  inversion L'; subst; clear L'.
    assert (X:= join_unit1_e _ _ H1 J'). subst.
    split; trivial.
    eapply join_canc. apply J'. assumption.
  apply False_ind. apply H1. trivial.
inversion L'; subst; clear L'.
  apply False_ind. apply H. trivial.
rewrite H4 in H0. inversion H0. subst.
destruct (join_assoc H2 J) as [u [I K]].
destruct (join_assoc H7 J') as [u' [I' K']].
destruct (rawnext_unique x' z z0 h0 h2 u u' r H1 H5 K K'). subst.
assert (u' = u).
  eapply join_canc. apply (join_comm K'). apply (join_comm K).
subst. clear K'.
destruct (IHL _ H6 _ _ I _ I'); subst; clear IHL H6.
split; trivial. eapply join_canc. apply J'. apply J.
Qed.

Lemma lseg_emp_at: forall h x y h1 (L:lseg x y h1) h2 (L2: lseg x y h2)
  h1' (J1:join h1 h1' h) h2' (J2: join h2 h2' h) l (E: emp_at l h2), emp_at l h1.
Proof.
intros h x y h1 L.
induction L; intros; subst.
  apply heap_gempty. apply H.
apply (emp_at_join H2).
split.
  inversion L2; subst; clear L2.
    apply False_ind. apply H. trivial.
  rewrite H0 in H4. inversion H4. apply eq_sym in H9. subst.
  apply (emp_at_join H7) in E. destruct E.
  assert (RNU: z0=z /\ h3=h0).
    destruct (join_assoc H2 J1) as [ss [J K]].
    destruct (join_assoc H7 J2) as [tt [JJ KK]].
    eapply (rawnext_unique _ _ _ _ _ _ _ h H1 H5 K KK).
  destruct RNU. subst. apply H8.
inversion L2; subst. clear L2.
    apply False_ind. apply H. trivial.
  rewrite H0 in H4. inversion H4. apply eq_sym in H9. subst.
  assert (RNU: z0=z /\ h3=h0).
    destruct (join_assoc H2 J1) as [ss [J K]].
    destruct (join_assoc H7 J2) as [tt [JJ KK]].
    eapply (rawnext_unique _ _ _ _ _ _ _ h H1 H5 K KK).
  destruct RNU; subst.
    assert (X:= IHL _ H6). clear IHL.
    destruct (join_assoc (join_comm H2) J1) as [t [J K]].
    assert (Y:= X _ K). clear X.
    destruct (join_assoc (join_comm H7) J2) as [u [JJ KK]].
    assert (Z:= Y _ KK). clear Y.
    apply Z. apply (emp_at_join H7). apply E.
Qed.

Lemma U4: forall x y z w sigma l s
  (SD1 : space_denote (Lseg x y :: Lseg y z :: sigma) s)
  (SD2: space_denote (Lseg x y :: Next z w :: l) s),
space_denote (Lseg x z :: sigma) s.
intros.
rewrite Space_denote_cons in SD1, SD2.
destruct SD1 as [s1 [s1' [J1 [K1 K1']]]].
destruct SD2 as [s2 [s2' [J2 [K2 K2']]]].
simpl in K1, K2.
repeat rewrite <- (expr_denote_join _ _ _ _ J1) in K1.
repeat rewrite <- (expr_denote_join _ _ _ _ J2) in K2.
assert (s2 = s1 /\ s2' = s1').
  assert (hp s2 = hp s1 /\ hp s2' = hp s1').
    eapply (lseg_unique _ _ _ K1 _ K2 (hp s1') (hp s)). apply J1. apply J2.
  destruct H as [HP1 HP2]. destruct s2. destruct s2'. destruct s1. destruct s1'.
    destruct (join_stacks_eq _ _ _ J1).
    destruct (join_stacks_eq _ _ _ J2).
    simpl in *. subst. subst. split; trivial.
destruct H; subst. clear J2 K2.
rewrite Space_denote_cons in K1', K2'.
destruct K1' as [t1 [t1' [I1 [G1 G1']]]].
destruct K2' as [t2 [t2' [I2 [G2 G2']]]].
simpl in G1.
repeat rewrite <- (expr_denote_join _ _ _ _ I1) in G1.
repeat rewrite <- (expr_denote_join _ _ _ _ (join_comm J1)) in G1.
simpl in G2. remember (val2loc (expr_denote z t2)) as b; destruct b; subst.
  destruct (join_assoc (join_comm I1) (join_comm J1)) as [u [JJ KK]].
  exists u. exists t1'. split. apply (join_comm KK).
  split; try assumption.
  eapply lseg_lseg_app. rewrite <- (expr_denote_join _ _ _ _ (join_comm KK)). apply K1.
                        rewrite <- (expr_denote_join _ _ _ _ (join_comm KK)). apply G1.
                        apply JJ.
    rewrite <- (expr_denote_join _ _ _ _ I2) in Heqb.
    rewrite <- (expr_denote_join _ _ _ _ (join_comm J1)) in Heqb.
    rewrite <- (expr_denote_join _ _ _ _ (join_comm KK)). rewrite <- Heqb. reflexivity.
    assert (emp_at l0 (hp s1)).
      destruct G2. apply rawnext2rawnext' in H.
          destruct (@rawnext_at1 _ _ _ (hp t2') (hp s1') H). apply I2.
          destruct (@rawnext_at1 _ _ _ (hp s1) (hp s) H2). apply join_comm. apply J1. assumption.
    eapply (@emp_at_join (hp t1) (hp s1) (hp u)). apply JJ.
    split; trivial.
    destruct (lseg_end _ _ _ G1).
       destruct H0. apply heap_gempty. apply H1.
       destruct H0. rewrite <- (expr_denote_join _ _ _ _ I2) in Heqb.
                    rewrite <- (expr_denote_join _ _ _ _ (join_comm J1)) in Heqb.
                    rewrite H0 in Heqb. rewrite nil_not_loc in Heqb. inversion Heqb.
       destruct H0 as [lc [vlc elc]]. rewrite <- (expr_denote_join _ _ _ _ I2) in Heqb.
                    rewrite <- (expr_denote_join _ _ _ _ (join_comm J1)) in Heqb.
                    rewrite vlc in Heqb. inversion Heqb. subst. assumption.
contradiction.
Qed.

Lemma unfolding4_sound' : forall  sigma2 sigma0 sigma1 sig2' s,
  In sig2' (unfolding4NPR' sigma0 sigma1 sigma2) ->
  space_denote sigma1 s -> space_denote sig2' s ->
  space_denote (sigma0++ sigma2) s.
Proof.
intros sigma2.
induction sigma2; simpl; intros; subst; simpl in *.
  contradiction.
rewrite <- (space_denote_permute _ _ (Permutation_middle sigma0 sigma2 a)).
destruct a; try apply (IHsigma2 _ _ _ _  H H0 H1).
destruct e; try apply (IHsigma2 _ _ _ _ H H0 H1).
destruct e0; try apply (IHsigma2 _ _ _ _ H H0 H1).
remember (lseg_in_dom2 v (Var v0) sigma1) as b.
  destruct b; subst; try apply (IHsigma2 _ _ _ _ H H0 H1).
  remember (next_in_dom v0 sigma1) as bb.
  destruct bb; subst; try apply (IHsigma2 _ _ _ _ H H0 H1).
  destruct H; try apply (IHsigma2 _ _ _ _ H H0 H1).
  rewrite <- H in *. clear H IHsigma2.
  rewrite space_insert in H1.
      assert (P: Permutation (Lseg (Var v) e
        :: insert (rev_cmp compare_space_atom)
             (Lseg e (Var v0)) (rev sigma0 ++ sigma2))
          (Lseg (Var v) e ::
            Lseg e (Var v0) :: (sigma0 ++ sigma2))).
        apply perm_skip. eapply perm_trans.
            apply perm_insert. apply perm_skip. apply Permutation_app_tail.
             apply Permutation_sym. apply Permutation_rev.
      rewrite (space_denote_permute _ _ P) in H1. clear P.
destruct (lseg_in_dom2Lemma_strong _ _ _ _ Heqb) as [sig1 [HSig1 Psig1]]. clear Heqb.
destruct (next_in_dom_true _ _ _ Heqbb H0) as [w [sig [SDsig Psig]]]. clear Heqbb.
remember v0 as z. clear Heqz v0.
  assert (PP: Permutation (Lseg (Var v) e :: sig1)  (Next (Var z) w :: sig)).
    eapply Permutation_trans. apply Permutation_sym. apply HSig1. apply Permutation_sym. apply Psig.
  clear Psig HSig1 H0.
  destruct (Perm_aux _ _ _ _ PP).
    destruct H. inversion H; subst.
destruct H as [l1 [l2 [Hsig1 Psig]]]. subst. clear PP.
remember v as x. clear Heqx v. remember e as y. clear Heqy e.
assert (P: Permutation (Next (Var z) w :: sig) (Lseg (Var x) y :: Next (Var z) w :: l1 ++ l2)).
  eapply Permutation_trans. apply perm_skip. apply Permutation_sym. apply Psig. apply perm_swap.
rewrite (space_denote_permute _ _ P) in SDsig. clear P. clear Psig sig.
apply (U4 (Var x) y (Var z) w (sigma0 ++ sigma2) _ _ H1 SDsig).
Qed.

Lemma unfolding4_sound: forall sc1 sc2 s
  (SC1: clause_denote sc1 s) (SC2: clause_denote sc2 s),
  listd clause_denote inter TT (unfolding4 sc1 sc2) s.
Proof.
intros.
destruct sc1; simpl; trivial.
destruct sc2; simpl; trivial.
rewrite (@listd_unfold_inter _ state).
eapply listd_inter_map.
  intros.
  simpl in *.
  intros.
  rewrite (@listd_unfold_inter _ state) in SC1,SC2,H0.
  rewrite listd_sort_uniq_inter in H0.
  assert (X: (forall x y : pure_atom, eq Eq (pure_atom_cmp x y) -> eq x y)).
      intros. apply pure_atom_cmp_eq. apply H1.
  assert (Y:= listd_sort_uniq_un pure_atom_denote FF pure_atom_cmp X).
  rewrite Y. clear X Y.
  destruct H0.
    rewrite listd_unfold_app_inter in H0.
    destruct H0.
    assert (SC1A: listd pure_atom_denote un (space_denote sigma) delta s).
      apply SC1. split. assumption. trivial. clear SC1.
    rewrite (@listd_unfold_un _ state) in SC1A.
    destruct SC1A.
      rewrite listd_unfold_app_un. left. assumption.
      assert (X:= unfolding4_sound' _ _ _ _ s H H3 H1). simpl in X.
      rewrite listd_unfold_app_un. right. apply SC2. split; assumption.
intros. apply pure_atom_cmp_eq. apply H1.
Qed.

Lemma U5_axiom: forall x y z w sigma' sigma h
  (K: (sepcon (lseg x y) (sepcon (lseg z w) sigma')) h)
  (K': (sepcon (lseg x y) (sepcon (lseg y z) sigma)) h),
  (z=w \/ (sepcon (lseg x z) sigma)  h).
Proof.
intros.
destruct K as [h1 [h1' [J1 [K1 K1']]]].
destruct K1' as [h2 [h2' [J2 [K2 K2']]]].
generalize dependent h.
generalize dependent h1.
generalize dependent h1'.
generalize dependent h2'.
generalize dependent sigma.
generalize dependent sigma'.
generalize dependent y.
generalize dependent x.
induction K2; intros; subst. left. trivial.
remember z as n. clear Heqn z.
remember x as z. clear Heqz x.
remember x0 as x. clear Heqx x0.
remember x' as zl. clear Heqzl x'.
remember y as w. clear Heqw y.
remember y0 as y. clear Heqy y0.
assert (emp_at zl h2). clear IHK2 K' K1 K2.
  destruct (join_assoc H2 J2) as [t [JJ TT]].
  destruct (join_assoc (join_comm TT) (join_comm J1)) as [u [II UU]].
  eapply rawnext_at1. eapply rawnext2rawnext'. apply H1. apply II.
clear IHK2.
right.
rewrite <- sepcon_assoc in K'.
destruct K' as [t1 [t1' [I1 [G1 G1']]]].
exists t1. exists t1'. split. assumption.
split; try assumption.
destruct G1 as [r1 [r1' [JJ1 [F1 F1']]]].
destruct (join_assoc JJ1 I1) as [u [JJ KK]].
destruct (lseg_unique x y _ K1 _ F1 _ _ J1 _ KK); subst. clear F1 KK.
eapply lseg_lseg_app. apply K1. apply F1'. apply join_comm. apply JJ1. apply H0.
apply (emp_at_join JJ1).
split. assumption.
destruct (lseg_end _ _ _ F1').
  destruct H4. eapply heap_gempty. apply H5.
  destruct H4. subst. rewrite nil_not_loc in H0. inversion H0.
  destruct H4 as [l [LL1 LL2]]. rewrite LL1 in H0. inversion H0. subst. apply LL2.
Qed.

Lemma U5: forall x y z w sigma1 sigma s
  (K: space_denote (Lseg x y :: Lseg z w :: sigma1) s)
  (K': space_denote (Lseg x y:: Lseg y z :: sigma) s),
pure_atom_denote (Eqv z w) s \/ space_denote (Lseg x z :: sigma) s.
Proof.
intros.
assert (UU:= U5_axiom (expr_denote x s) (expr_denote y s)
                           (expr_denote z s) (expr_denote w s)
    (fun h => space_denote sigma1 (State (stk s) h))
    (fun h => space_denote sigma (State (stk s) h)) (hp s)).
destruct UU.
  clear K'. simpl in K.
  destruct K as [s1 [s2 [J [K KK]]]].
  exists (hp s1). exists (hp s2). split. apply J.
  repeat rewrite <- (expr_denote_join _ _ _ _ J) in K.
  split. apply K.
  destruct KK as [s1' [s2' [J' [K' KK']]]].
  repeat rewrite <- (expr_denote_join _ _ _ _ J') in K'.
  repeat rewrite <- (expr_denote_join _ _ _ _ (join_comm J)) in K'.
  exists (hp s1'). exists (hp s2'). split. apply J'.
  split. apply K'.
  destruct s2'. destruct (join_stacks_eq _ _ _ J'). destruct (join_stacks_eq _ _ _ J).
     simpl in *. rewrite <- H in *. rewrite H0 in *. rewrite <- H1 in *. rewrite H2 in *. assumption.

  clear K. simpl in K'. remember K' as K. clear HeqK K'.
  destruct K as [s1 [s2 [J [K KK]]]].
  exists (hp s1). exists (hp s2). split. apply J.
  repeat rewrite <- (expr_denote_join _ _ _ _ J) in K.
  split. apply K.
  destruct KK as [s1' [s2' [J' [K' KK']]]].
  repeat rewrite <- (expr_denote_join _ _ _ _ J') in K'.
  repeat rewrite <- (expr_denote_join _ _ _ _ (join_comm J)) in K'.
  exists (hp s1'). exists (hp s2'). split. apply J'.
  split. apply K'.
  destruct s2'. destruct (join_stacks_eq _ _ _ J'). destruct (join_stacks_eq _ _ _ J).
     simpl in *. rewrite <- H in *. rewrite H0 in *. rewrite <- H1 in *. rewrite H2 in *. assumption.

left. apply H.
right. rewrite Space_denote_cons. simpl.  clear K K'.
  destruct H as [s1 [s2 [J [K KK]]]].
  assert (join (State (stk s) s1) (State (stk s) s2) s).
    split. simpl. apply sepalg_generators.join_equiv_refl.  apply J.
  exists (State (stk s) s1).
  exists (State (stk s) s2).
  split. assumption.
  split; trivial.
Qed.

Lemma unfolding6NPR'_sound: forall  sigma2 sigma0 sigma1 sig2' p s,
  In (p,sig2') (unfolding6NPR' sigma0 sigma1 sigma2) ->
  space_denote sigma1 s -> space_denote sig2' s ->
  pure_atom_denote p s \/ (space_denote (sigma0++ sigma2)) s.
Proof.
intros sigma2.
induction sigma2; simpl; intros; subst; simpl in *.
  contradiction.
rewrite <- (space_denote_permute _ _ (Permutation_middle sigma0 sigma2 a)).
destruct a; try apply (IHsigma2 _ _ _ _ _ H H0 H1).
destruct e; try apply (IHsigma2 _ _ _ _ _ H H0 H1).
destruct e0; try apply (IHsigma2 _ _ _ _ _ H H0 H1).
remember v0 as z. clear Heqz v0.
remember (Ident.eq_dec v z) as bv; destruct bv; subst; simpl.
  assert (X:= IHsigma2 _ _ _ _ _ H H0 H1); clear IHsigma2.
  destruct X. left; trivial.
  right. destruct (join_ex_identities s) as [sid [Esid [ss Hss]]].
         rewrite (join_unit1_e _ _ Esid Hss).
         exists sid. exists s. split; trivial. split; trivial.
           apply lseg_nil. apply empstate_empheap. assumption.
             apply var_nil_or_loc.
remember (lseg_in_dom2 v (Var z) sigma1 ) as b.
destruct b; subst; try apply (IHsigma2 _ _ _ _ _ H H0 H1).
destruct (in_app_or _ _ _ H); clear H; try apply (IHsigma2 _ _ _ _ _ H2 H0 H1).
(*In map..*)
clear IHsigma2.
destruct (@in_map_iff pure_atom (prod pure_atom (list space_atom))
                (fun atm : pure_atom =>
           (atm,
            insert (rev_cmp compare_space_atom) (Lseg (Var v) e)
                (insert (rev_cmp compare_space_atom) (Lseg e (Var z))
                   (app (rev sigma0) sigma2)))) (lseg_in_dom_atoms z sigma1) (p, sig2')) as [K1 _].
destruct (K1 H2) as [pa [K2 K3]].
inversion K2; subst. clear K1 K2 H2.
destruct (lseg_in_dom_atoms_space_denote_perm_strong _ _ _ _ H0 K3) as [w [SP1 [SP2 | [sig1 [SD P]]]]].
  left. assumption.
rewrite space_insert in H1.
      assert (PP: Permutation (Lseg (Var v) e
        :: insert (rev_cmp compare_space_atom)
             (Lseg e (Var z)) (rev sigma0 ++ sigma2))
          (Lseg (Var v) e
        :: [Lseg e (Var z)] ++ (sigma0 ++ sigma2))).
        apply perm_skip. eapply perm_trans. apply perm_insert.
          apply perm_skip. apply Permutation_app_tail.
          apply Permutation_sym. apply Permutation_rev.
      rewrite (space_denote_permute _ _ PP) in H1. clear PP.
remember v as x. clear Heqx v. remember e as y. clear Heqy e.
destruct (lseg_in_dom2Lemma_strong _ _ _ _ Heqb) as [sig [Hsig EQ]]; clear Heqb.
assert (PP: Permutation (Lseg (Var z) w :: sig1)  (Lseg (Var x) y :: sig)).
    eapply Permutation_trans. apply Permutation_sym. apply P. apply Hsig.
destruct (Perm_aux _ _ _ _ PP).
    destruct H. inversion H; subst. clear H.
      exfalso. apply n. trivial.
destruct H as [l1 [l2 [Sig HP]]]. subst.
  assert (PPP: Permutation (Lseg (Var z) w :: l1 ++ Lseg (Var x) y :: l2) (Lseg (Var x) y :: Lseg (Var z) w :: l1 ++  l2)).
      apply Permutation_sym. eapply Permutation_trans. apply perm_swap. apply perm_skip. apply Permutation_middle.
  rewrite (space_denote_permute _ _ PPP) in SD.
  assert (U:= U5 (Var x) y (Var z) w (l1 ++ l2) (sigma0 ++ sigma2) s SD H1).
  destruct U. left. destruct SP1; subst.  apply H. simpl. apply var_eq_sym. apply H.
  right. trivial.
Qed.

Lemma unfolding6_sound: forall sc1 sc2 s
  (SC1: clause_denote sc1 s) (SC2: clause_denote sc2 s),
  listd clause_denote inter TT (unfolding6 sc1 sc2) s.
Proof.
intros.
destruct sc1; simpl; trivial.
destruct sc2; simpl; trivial.
rewrite (@listd_unfold_inter _ state).
eapply listd_inter_map.
  intros. destruct x.
  simpl in *.
  intros.
  rewrite (@listd_unfold_inter _ state) in SC1,SC2,H0.
  destruct H0.
  rewrite (listd_insert_uniq_un pure_atom_denote).
  rewrite listd_sort_uniq_un.
  rewrite listd_sort_uniq_inter in H0.
  rewrite listd_app in H0.
  rewrite (@listd_unfold_inter _ state) in H0.
  destruct H0.
  assert (SC1A: listd pure_atom_denote un (space_denote sigma) delta s).
    apply SC1. split.  assumption.  trivial. clear SC1.
  rewrite (@listd_unfold_un _ state) in SC1A.
  destruct SC1A.
    right. rewrite listd_app. rewrite (@listd_unfold_un _ state). left. assumption.
   destruct (unfolding6NPR'_sound _ _ _ _ _ s H H3 H1); clear H H1 H3.
    left. rewrite <- pure_atom_denote_order_eqv_pure_atom. apply H4.
  simpl in H4.
    assert (listd pure_atom_denote un FF delta0 s).
      apply SC2. split; assumption.
    rewrite (@listd_unfold_un _ state) in H|-*.
    destruct H. right. left.
         rewrite listd_app.
         rewrite (@listd_unfold_un _ state). right. apply H.
         contradiction.
intros. do_comp pure_atom_cspec x y; try congruence.
intros. do_comp pure_atom_cspec x y; try congruence.
intros. do_comp pure_atom_cspec x y; try congruence.
Qed.

(*an axiom schema for an additional (but apparently superfluous) rule eliminating loops in lsegs*)
Lemma U7_axiomSchema: forall x y z u Sigma s,
  space_denote (Lseg y z::Lseg z y::Lseg x y::Lseg u z::Sigma) s ->
  space_denote (Lseg x z::Lseg u y::Sigma) s.
Proof.
intros.
repeat rewrite Space_denote_cons.
repeat rewrite Space_denote_cons in H.
destruct H as [st1 [st1' [J1 [K1 K1']]]].
destruct K1' as [st2 [st2' [J2 [K2 K2']]]].
inversion K1; subst.
   rewrite <- (expr_denote_join z _ _ _ J1) in H. rewrite <- (expr_denote_join y _ _ _ J1) in H.
  apply join_unit1_e in J1. subst.
  inversion K2; subst.
    apply join_unit1_e in J2. subst.
    destruct K2' as [st3 [st3' [J3 [K3 K3']]]].
    destruct K3' as [st4 [st4' [J4 [K4 K4']]]].
    rewrite <- (var_eq_Lseg2 x z y st3) in K3.
    rewrite (var_eq_Lseg2 u z y st4) in K4.
    exists st3. exists st3'. split. assumption. split. assumption.
    exists st4. exists st4'. split. assumption. split; assumption.
   unfold var_eq. rewrite <- (expr_denote_join z _ _ _ J4). rewrite <- (expr_denote_join y _ _ _ J4).
           rewrite <- (expr_denote_join z _ _ _ (join_comm J3)). rewrite <- (expr_denote_join y _ _ _ (join_comm J3)).
           rewrite H. trivial.
   unfold var_eq. rewrite <- (expr_denote_join z _ _ _ J3). rewrite <- (expr_denote_join y _ _ _ J3).
           rewrite H. trivial.
   rewrite empstate_empheap. apply H3.
 rewrite <- (expr_denote_join z _ _ _ J2) in H1. rewrite <- (expr_denote_join y _ _ _ J2) in H1.
   apply False_ind. apply H1. rewrite H. trivial.
 rewrite empstate_empheap. apply H0.
(*y<>z*)
  rewrite <- (expr_denote_join z _ _ _ J1) in H. rewrite <- (expr_denote_join y _ _ _ J1) in H.
  inversion K2; subst.
    rewrite <- (expr_denote_join z _ _ _ J2) in H4. rewrite <- (expr_denote_join y _ _ _ J2) in H4.
    rewrite <- (expr_denote_join z _ _ _ (join_comm J1)) in H4. rewrite <- (expr_denote_join y _ _ _ (join_comm J1)) in H4.
    apply False_ind. apply H. rewrite H4. trivial.
  destruct K2' as [st3 [st3' [J3 [K3 K3']]]].
  destruct K3' as [st4 [st4' [J4 [K4 K4']]]].
   destruct (join_assoc J3 (join_comm J2)) as [st5 [J5 J5']].
   destruct (join_assoc (join_comm J5') (join_comm J1)) as [st6 [J6 J6']].
   exists st6. exists st5. split. apply join_comm. apply J6'.
   split. eapply (lseg_lseg_app (expr_denote x st6) (expr_denote y st6) (expr_denote z st6) (hp st3) (hp st1)).
            rewrite (expr_denote_join x _ _ _ J6). rewrite (expr_denote_join y _ _ _ J6). apply K3.
            rewrite (expr_denote_join y _ _ _ (join_comm J6)). rewrite (expr_denote_join z _ _ _ (join_comm J6)). apply K1.
            apply join_comm. apply J6.
            rewrite (expr_denote_join z _ _ _ (join_comm J6)). rewrite <- (expr_denote_join z _ _ _ J1).
              rewrite <- (expr_denote_join z _ _ _ (join_comm J5)) in H5.
              rewrite <- (expr_denote_join z _ _ _ (join_comm J5')) in H5.
              rewrite <- (expr_denote_join z _ _ _ (join_comm J1)) in H5. apply H5.
            destruct (join_assoc J5 J6') as [st7 [J7 J7']]. destruct J7.
                destruct (join_assoc (join_comm H8) H10) as [st8 [J8 J8']].
              eapply rawnext_at1. eapply rawnext2rawnext'. apply H6. apply J8.
   destruct (join_assoc J4 (join_comm J3)) as [st7 [J7 J7']].
   destruct (join_assoc (join_comm J7') (join_comm J2)) as [st8 [J8 J8']].
   assert (SD: space_atom_denote (Lseg u y) st8).
       eapply (lseg_lseg_app (expr_denote u st8) (expr_denote z st8) (expr_denote y st8) (hp st4) (hp st2)).
            rewrite (expr_denote_join u _ _ _ J8). rewrite (expr_denote_join z _ _ _ J8). apply K4.
            rewrite (expr_denote_join z _ _ _ (join_comm J8)). rewrite (expr_denote_join y _ _ _ (join_comm J8)). apply K2.
            apply join_comm. apply J8.
            rewrite (expr_denote_join y _ _ _ (join_comm J8)). rewrite <- (expr_denote_join y _ _ _ J2).
              rewrite <- (expr_denote_join y _ _ _ (join_comm J1)). rewrite <- (expr_denote_join y _ _ _ J1) in H0. apply H0.
            destruct J1 as [JJ1 JJ1'].
            destruct (join_assoc (join_comm H3) JJ1') as [st9 [J9 J9']]. destruct J8' as [JJ8 JJ8'].
            destruct (join_assoc JJ8' (join_comm J9)) as [st10 [J10 J10']].
            eapply rawnext_at1. eapply rawnext2rawnext'. apply H1. eapply join_comm. apply J10.
    exists st8. exists st4'.
    split.
      destruct (join_assoc (join_comm J7) J8') as [st9 [J9 J9']].
      assert (X:= join_canc (join_comm J9') (join_comm J5')). subst.
      apply join_comm. apply J9.
    split; assumption.
Qed.

Lemma clause_setd_listd l s :
  listd clause_denote inter TT l s ->
  setd clause_denote inter TT (clause_list2set l) s.
Proof with simpl; auto; try solve[congruence].
intro H1. apply setd_fold_left... intros c cls s0 H2 H3; apply setd_add...
unfold setd; rewrite empty_set_elems...
Qed.

Local Notation listd_unfold_state := (@listd_unfold_inter _ state).

Lemma do_unfold'_sound c1 c2 al s:
  clause_denote c1 s -> clause_denote c2 s ->
  listd clause_denote inter TT al s ->
  listd clause_denote inter TT (do_unfold' c1 c2 al) s.
Proof with auto.
intros H0 H1 H2. unfold do_unfold'.
rewrite listd_app, listd_unfold_state; split. solve[apply unfolding1_sound;auto].
rewrite listd_app, listd_unfold_state; split. solve[apply unfolding2_sound;auto].
rewrite listd_app, listd_unfold_state; split. solve[apply unfolding3_sound;auto].
rewrite listd_app, listd_unfold_state; split. solve[apply unfolding4_sound;auto].
rewrite listd_app, listd_unfold_state; split. solve[apply unfolding6_sound;auto].
auto.
Qed.

Lemma add_list_simpl_aux: forall l s s',
  M.Equal s s' ->
  M.Equal (add_list_to_set_simple l s) (add_list_to_set_simple l s').
Proof.
induction l; simpl; intros; auto. apply IHl.
unfold Basics.flip.
intro y.
rewrite (M.add_spec s); rewrite (M.add_spec s').
specialize (H y).
intuition.
Qed.

Lemma add_list_to_set_spec1:
  forall l s s', add_list_to_set l s = Some s' ->
           M.Equal (add_list_to_set_simple l s) s'.
Proof.
  induction l; simpl; intros. inversion H.
  revert H; case_eq (mem_add a s); intros. inversion H0; clear H0; subst.
  unfold mem_add in H. if_tac in H; inversion H; clear H; subst.
  clear.
  apply add_list_simpl_aux. reflexivity.
  unfold mem_add in H.
  revert H; case_eq (M.mem a s); intros. clear H1.
  specialize (IHl _ _ H0).
  etransitivity; try apply IHl.
  apply add_list_simpl_aux.
  clear - H; intro y.
  unfold Basics.flip. rewrite M.add_spec.
  intuition. subst; auto.
 rewrite M.mem_spec in H; auto.
  inversion H1.
Qed.

Lemma add_list_to_set_spec2:
  forall l s, add_list_to_set l s = None ->
                       Forall (fun x => M.In x s) l.
Proof.
 induction l; simpl; intros.
 constructor.
 revert H; case_eq (mem_add a s); intros; try discriminate.
 unfold mem_add in H. revert H; case_eq (M.mem a s); intros; try discriminate.
 specialize (IHl _ H0).
 constructor; auto.
 rewrite <- M.mem_spec; auto.
Qed.

Lemma add_list_union:
  forall l s, M.Equal (add_list_to_set_simple l s)
                      (M.union (clause_list2set l) s).
Proof.
 unfold clause_list2set.
  unfold add_list_to_set_simple.
  change  (fun (s0 : M.t) (c : M.elt) => M.add c s0) with (Basics.flip M.add).
 induction l; simpl; intros; auto.
  intro y; rewrite M.union_spec. intuition.
 apply M.empty_spec in H0. contradiction.
  rewrite IHl; clear IHl.
  unfold Basics.flip at 2 4.
  remember (M.empty) as s'. clear Heqs'.
  revert a s s'; induction l; simpl; intros.
  intro y. repeat rewrite M.union_spec.
  repeat rewrite M.add_spec. intuition.
  rewrite IHl; clear IHl.
  unfold Basics.flip at 2 4.
  assert (M.Equal (M.add a0 (M.add a s')) (M.add a (M.add a0 s'))).
  intro y; repeat rewrite M.add_spec; intuition.
  generalize (add_list_simpl_aux l _ _ H); intro.
  intro y; specialize (H0 y).
  repeat rewrite M.union_spec; intuition.
 Qed.

Lemma perm_exists: forall {A} (l:list A) a, In a l ->
  exists l', Permutation l (a::l').
Proof.
intros A l.
induction l; simpl; intros. contradiction.
destruct H; subst.
  exists l. apply Permutation_refl.
destruct (IHl _ H).
  exists (a::x).
  eapply Permutation_trans. apply perm_skip. apply H0.
  apply perm_swap.
Qed.

Lemma listd_cong1: forall l' l st,
  (forall x, In x l' -> In x l) ->
  listd clause_denote inter TT l st -> listd clause_denote inter TT l' st.
Proof.
intros l'.
induction l'; intros; subst; simpl in *.
  assert (X:= listd_unfold_inter clause_denote TT l). unfold pred in X. rewrite X in H0.
     destruct H0. assumption.
assert (Y: forall x : clause, In x l' -> In x l).
  intros. apply H. right. trivial.
assert (X:= IHl' l st Y H0). clear IHl' Y.
split; try assumption.
assert (In a l). apply H. left. trivial.
clear X H.
destruct (perm_exists _ _ H1) as [l'' Hl''].
rewrite (listd_perm clause_denote inter TT interS interA _ _ Hl'') in H0.
rewrite listd_cons in H0.
destruct H0.
assumption.
Qed.

Lemma listd_cong: forall l' l st,
  (forall x, In x l' <-> In x l) ->
  (listd clause_denote inter TT l st <-> listd clause_denote inter TT l' st).
Proof.
intros.
split; intros.
  eapply (listd_cong1 _ l). intros. apply H. assumption. assumption.
  eapply (listd_cong1 _ l'). intros. apply H. assumption. assumption.
Qed.

Lemma MEqual_InElem1: forall s t,
  M.Equal s t ->
  forall x, In x (M.elements s) -> In x (M.elements t).
Proof.
intros.
apply Melements_spec1 in H0.
apply  Melements_spec1.
apply H. apply H0.
Qed.

Lemma MEqual_InElem2: forall s t,
  M.Equal s t ->
  forall x, In x (M.elements t) -> In x (M.elements s).
Proof.
intros.
apply Melements_spec1 in H0.
apply  Melements_spec1.
apply H. apply H0.
Qed.

Lemma MEqual_InElem: forall s t,
  M.Equal s t ->
  forall x, In x (M.elements t) <-> In x (M.elements s).
Proof.
intros.
split; intros. eapply (MEqual_InElem2 _ _ H _ H0). eapply (MEqual_InElem1 _ _ H _ H0).
Qed.

Lemma MEqual_MIn: forall s t,
  M.Equal s t ->
  forall x, M.In x s <-> M.In x t.
Proof.
intros.
split; intros; apply Melements_spec1; apply Melements_spec1 in H0;
  eapply (MEqual_InElem s t H); apply H0.
Qed.

Lemma setd_cong: forall s t st,
  M.Equal s t ->
  setd clause_denote inter TT s st -> setd clause_denote inter TT t st.
Proof.
intros.
unfold setd in *.
eapply (listd_cong1 _ (M.elements s)); try assumption.
  intros.
eapply MEqual_InElem2. apply H. apply H1.
Qed.

Lemma do_unfold_sound n c s s' st :
  clause_denote c st -> setd clause_denote inter TT s st ->
  do_unfold n c s = s' ->
  setd clause_denote inter TT s' st.
Proof with simpl; auto; try solve[congruence].
revert s s'; induction n... intros s s' H1 H2.
case_eq (add_list_to_set (M.fold (do_unfold' c) s []) s); intros.
apply add_list_to_set_spec1 in H.
rewrite add_list_union in H.
apply (IHn t s'); auto.
eapply setd_cong. apply H.
apply setd_un...
apply clause_setd_listd...
rewrite M.fold_spec.
apply listd_fold_left... intros c' cls H3 H4.
unfold Basics.flip.
apply do_unfold'_sound...
subst s'; auto.
Qed.

Lemma spatial_resolution_sound':
  forall nc pc s,
     clause_denote nc s -> clause_denote pc s ->
        setd clause_denote inter TT (spatial_resolution nc pc) s.
Proof.
intros.
assert (forall c, spatial_resolution nc pc = M.singleton c -> clause_denote c s).
intros. eapply spatial_resolution_sound in H1; eauto.
clear H H0.
destruct nc; simpl in *; try apply setd_empty_set.
destruct pc; simpl in *; try apply setd_empty_set.
if_tac; simpl in *; try apply setd_empty_set.
unfold setd. rewrite elements_singleton. simpl. split; auto.
Qed.

Lemma unfolding_sound c1 c2 s :
  clause_denote c1 s -> clause_denote c2 s ->
  setd clause_denote inter TT (unfolding c1 c2) s.
Proof with simpl; auto; try solve[congruence].
unfold unfolding; intros H1 H2.
generalize (do_unfold_sound 500 c1 (M.add c2 M.empty)
  (do_unfold 500 c1 (M.add c2 M.empty)) s H1) as H3; intro.
spec H3.  apply setd_add; auto. apply setd_empty_set; auto.
spec H3.
remember (do_unfold 500 c1 (M.add c2 M.empty)) as J.
clear - H1 H3; auto.
remember (do_unfold 500 c1 (M.add c2 M.empty)) as J.
rewrite M.fold_spec.
unfold setd in *.
remember (@TT state) as b.
clear Heqb.
unfold Basics.flip; rewrite <- fold_left_rev_right.
rewrite (@listd_unfold_inter M.elt state) in H3|-*.
destruct H3; split; auto.
rewrite <- (@listd_inter_rev _ state) in H.
revert H. induction (rev (M.elements J)); intros.
simpl. rewrite empty_set_elems. auto.
simpl in H.
destruct H.
specialize (IHl H3).
clear H2.
simpl.
apply setd_un.
apply spatial_resolution_sound'; auto.
auto.
Qed.

End UF_Sound.