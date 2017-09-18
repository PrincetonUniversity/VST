Require Import Coq.Sorting.Permutation.
Require Import VST.veric.base.
Require Import VST.veric.Clight_lemmas.

(* TODO: This is obviously true. Ask Xavior to remove the definition list_norepet.*)
Axiom list_norepet_NoDup: forall {A: Type} (l: list A), list_norepet l <-> NoDup l.

Lemma PTree_In_fst_elements {A: Type}: forall (T: PTree.t A) i,
  In i (map fst (PTree.elements T)) <-> exists a, PTree.get i T = Some a.
Proof.
  intros.
  split; intros.
  + apply list_in_map_inv in H.
    destruct H as [[i0 a] [? ?]].
    simpl in H; subst i0.
    apply PTree.elements_complete in H0.
    eauto.
  + destruct H as [a ?].
    apply PTree.elements_correct in H.
    apply (in_map fst) in H.
    auto.
Qed.

Lemma PTree_gs {A: Type}: forall (T: PTree.t A) i j x,
  (exists a, PTree.get i T= Some a) ->
  exists a, PTree.get i (PTree.set j x T) = Some a.
Proof.
  intros.
  destruct H.
  destruct (Pos.eq_dec i j).
  + subst.
    rewrite PTree.gss; eauto.
  + rewrite PTree.gso; eauto.
Qed.

Lemma PTree_gs_equiv {A: Type}: forall (T: PTree.t A) i j x,
  (exists a, PTree.get i T= Some a) \/ i = j <->
  exists a, PTree.get i (PTree.set j x T) = Some a.
Proof.
  intros.
  split; intros.
  + destruct H; [apply PTree_gs; auto |].
    subst; rewrite PTree.gss; eauto.
  + destruct (Pos.eq_dec i j); auto.
    rewrite PTree.gso in H by auto.
    auto.
Qed.

Lemma PTree_set_In_fst_elements {A: Type}: forall (T: PTree.t A) i i' a',
  In i (map fst (PTree.elements T)) ->
  In i (map fst (PTree.elements (PTree.set i' a' T))).
Proof.
  intros.
  rewrite PTree_In_fst_elements in H |- *.
  apply PTree_gs; auto.
Qed.
  
Fixpoint relative_defined_type {A: Type} (l: list (ident * A)) (t: type): Prop :=
  match t with
  | Tarray t' _ _ => relative_defined_type l t'
  | Tstruct id _ => In id (map fst l)
  | Tunion id _ => In id (map fst l)
  | _ => True
  end.

Lemma relative_defined_type_mono: forall {A B: Type} (l1: list (ident * A)) (l2: list (ident * B)) (t: type),
  (forall i, In i (map fst l1) -> In i (map fst l2)) ->
  relative_defined_type l1 t ->
  relative_defined_type l2 t.
Proof.
  intros.
  induction t; auto.
  + simpl in *.
    firstorder.
  + simpl in *.
    firstorder.
Qed.

Lemma relative_defined_type_equiv: forall {A B: Type} (l1: list (ident * A)) (l2: list (ident * B)) (t: type),
  (forall i, In i (map fst l1) <-> In i (map fst l2)) ->
  (relative_defined_type l1 t <-> relative_defined_type l2 t).
Proof.
  intros.
  split; apply relative_defined_type_mono;
  firstorder.
Qed.

Definition PTree_get_list {A: Type} (i: positive) (T: PTree.t (list A)): list A :=
  match PTree.get i T with
  | Some l => l
  | None => nil
  end.

Definition PTree_set_cons {A: Type} (i: positive) (a: A) (T: PTree.t (list A)) :=
  PTree.set i (a :: PTree_get_list i T) T.

Lemma PTree_set_cons_Permutation {A: Type}: forall i a (T: PTree.t (list A)),
  Permutation (a :: concat (map snd (PTree.elements T)))
              (concat (map snd (PTree.elements (PTree_set_cons i a T)))).
Proof.
  intros.
  assert (exists l1 l2,
             map snd (PTree.elements (PTree_set_cons i a T)) =
             l1 ++ (a :: PTree_get_list i T) :: l2 /\
             map snd (PTree.elements (PTree.remove i (PTree_set_cons i a T))) =
             l1 ++ l2
         ).
  Focus 1. {
    pose proof @PTree.elements_remove _ i  (a :: PTree_get_list i T) (PTree_set_cons i a T).
    unfold PTree_set_cons in H at 1.
    rewrite PTree.gss in H.
    specialize (H eq_refl).
    destruct H as [l1 [l2 [? ?]]].
    exists (map snd l1), (map snd l2).
    split.
    + rewrite H.
      rewrite map_app; auto.
    + rewrite H0.
      rewrite map_app; auto.
  } Unfocus.
  assert (exists l1 l2,
             (map snd (PTree.elements T) =
             l1 ++ PTree_get_list i T :: l2 \/
             map snd (PTree.elements T) = l1 ++ l2 /\
             PTree_get_list i T = nil)
             /\
             map snd (PTree.elements (PTree.remove i T)) =
             l1 ++ l2
         ).
  Focus 1. {
    clear H.
    destruct (T ! i) eqn:?H.
    + pose proof @PTree.elements_remove _ i (PTree_get_list i T) T.
      unfold PTree_get_list in H0 at 1; rewrite H in H0.
      specialize (H0 eq_refl).
      destruct H0 as [l1 [l2 [? ?]]].
      exists (map snd l1), (map snd l2).
      split.
      - rewrite H0.
        rewrite map_app; auto.
      - rewrite H1.
        rewrite map_app; auto.
    + exists nil, (map snd (PTree.elements T)).
      replace (PTree.elements (PTree.remove i T)) with (PTree.elements T).
      Focus 2. {
        apply PTree.elements_extensional; intros.
        rewrite PTree.grspec.
        if_tac; auto.
        subst; auto.
      } Unfocus.
      split; auto.
      right.
      split; auto.
      unfold PTree_get_list; rewrite H; auto.
  } Unfocus.
  destruct H0 as [l11 [l12 [? ?]]], H as [l21 [l22 [? ?]]].
  assert (PTree.elements (PTree.remove i T) = PTree.elements (PTree.remove i (PTree_set_cons i a T))).
  Focus 1. {
    apply PTree.elements_extensional; intros.
    unfold PTree_set_cons.
    rewrite !PTree.grspec.
    if_tac; auto.
    rewrite PTree.gso by auto; auto.
  } Unfocus.
  rewrite H3, H2 in H1.
  clear H2 H3.
  rewrite H; clear H.
  assert (concat (map snd (PTree.elements T)) = concat (l11 ++ PTree_get_list i T :: l12)).
  Focus 1. {
    destruct H0 as [? | [? ?]].
    + rewrite H; auto.
    + rewrite H0, H.
      rewrite !concat_app.
      auto.
  } Unfocus.
  rewrite H; clear H H0.
  rewrite !concat_app; simpl.
  rewrite app_comm_cons.
  rewrite app_assoc.
  rewrite (Permutation_app_tail _ (Permutation_app_comm _ _)).
  rewrite <- app_assoc; simpl.
  rewrite <- concat_app, <- H1, concat_app.
  rewrite !app_comm_cons, !app_assoc.
  apply Permutation_app_tail.
  change (a :: concat l21) with ((a :: nil) ++ concat l21).
  rewrite app_assoc.
  rewrite Permutation_app_comm.
  apply Permutation_app_head.
  apply Permutation_app_comm.
Qed.

Module composite_reorder.
Section composite_reorder.

Context (l: list (positive * composite)).

Definition rebuild_composite_tree: PTree.t (list (ident * composite)) :=
  fold_right (fun ic => PTree_set_cons (Pos.of_succ_nat (co_rank (snd ic))) ic) (PTree.empty _) l.

Definition max_rank_composite: nat :=
  fold_right (fun ic => max (co_rank (snd ic))) O l.

Definition rebuild_composite_elements: list (ident * composite) :=
  let RCT := rebuild_composite_tree in
  (fix rebuild_composite_elements_rec (n: nat): list (ident * composite) :=
    match n with
    | O => nil
    | S n' => PTree_get_list (Pos.of_succ_nat n') RCT ++ rebuild_composite_elements_rec n'
    end) max_rank_composite.

Lemma rebuild_composite_tree_Permutation:
  Permutation l (concat (map snd (PTree.elements rebuild_composite_tree))).
Proof.
  intros.
  unfold rebuild_composite_tree.
  induction l.
  + simpl.
    apply Permutation_refl.
  + simpl.
    rewrite perm_skip; [clear IHl0 | apply IHl0].
    apply PTree_set_cons_Permutation.
Qed.

Lemma rebuild_composite_tree_correct:
  forall r i co,
    In (i, co) (PTree_get_list (Pos.of_succ_nat r) rebuild_composite_tree) ->
    co_rank co = r.
Proof.
  unfold rebuild_composite_tree.
  revert l; intro L; induction L; intros.
  + simpl in H.
    unfold PTree_get_list in H.
    rewrite PTree.gempty in H.
    inv H.
  + destruct a as [i0 co0].
    simpl in H.
    unfold PTree_get_list, PTree_set_cons in H.
    destruct (Pos.eq_dec (Pos.of_succ_nat (co_rank co0)) (Pos.of_succ_nat r)).
    - rewrite e, PTree.gss in H.
      destruct H.
      * inv H.
        apply SuccNat2Pos.inj; auto.
      * eapply IHL; eauto.
    - rewrite PTree.gso in H by auto.
      eapply IHL; eauto.
Qed.

Lemma max_rank_composite_is_upper_bound: forall env i co,
  PTree.get i env = Some co ->
  (co_rank co <= max_rank_composite env)%nat.
Proof.
  intros.
  apply PTree.elements_correct in H.
  unfold max_rank_composite.
  induction (PTree.elements env).
  + inv H.
  + destruct H.
    - subst.
      simpl.
      apply Max.le_max_l.
    - apply IHl in H.
      etransitivity; [exact H |].
      simpl.
      apply Max.le_max_r.
Qed.

Inductive ordered_composite: list (positive * composite) -> Prop :=
| ordered_composite_nil: ordered_composite nil
| ordered_composite_cons: forall i co l,
    Forall (relative_defined_type l) (map snd (co_members co)) ->
    ordered_composite l ->
    ordered_composite ((i, co) :: l).

Module type_func.
Section type_func.

Context {A: Type}
        (f_default: type -> A)
        (f_array: A -> Z -> attr -> A)
        (f_struct: A -> attr -> A)
        (f_union: A -> attr -> A)
        (f_member: struct_or_union -> list (ident * A) -> A).

Fixpoint F (env: PTree.t A) (t: type): A :=
  match t with
  | Tarray t n a => f_array (F env t) n a
  | Tstruct id a =>
      match env ! id with
      | Some v => f_struct v a
      | None => f_default t
      end
  | Tunion id a =>
      match env ! id with
      | Some v => f_union v a
      | None => f_default t
      end
  | _ => f_default t
  end.

Definition Completeness (cenv: composite_env) (env: PTree.t A): Prop :=
  forall i co,
    PTree.get i cenv = Some co ->
    exists a, PTree.get i env = Some a.

Definition Consistency (cenv: composite_env) (env: PTree.t A): Prop :=
  forall i co a,
    PTree.get i cenv = Some co ->
    PTree.get i env = Some a ->
    a = f_member (co_su co) (map
                              (fun it0: positive * type =>
                                 let (i0, t0) := it0 in
                                 (i0, F env t0))
                              (co_members co)).

Definition env_rec (i: positive) (co: composite) (env: PTree.t A): PTree.t A :=
  PTree.set i
    (f_member (co_su co) (map
                              (fun it0: positive * type =>
                                 let (i0, t0) := it0 in (i0, F env t0))
                              (co_members co)))
    env.

Definition Env (l: list (positive * composite)): PTree.t A :=
  fold_right
    (fun (ic: positive * composite) =>
       let (i, co) := ic in env_rec i co)
    (PTree.empty A)
    l.

Lemma F_PTree_set: forall t env i a,
  ~ In i (map fst (PTree.elements env)) ->
  relative_defined_type (PTree.elements env) t ->
  F env t = F (PTree.set i a env) t.
Proof.
  intros.
  induction t; auto.
  + simpl.
    apply IHt in H0.
    rewrite H0; auto.
  + simpl in H0 |- *.
    rewrite PTree.gso; auto.
    intro; subst; tauto.
  + simpl in H0 |- *.
    rewrite PTree.gso; auto.
    intro; subst; tauto.
Qed.    

Lemma relative_defined_type_PTree_set: forall t (env: PTree.t A) i a,
  relative_defined_type (PTree.elements env) t ->
  relative_defined_type (PTree.elements (PTree.set i a env)) t.
Proof.
  intros.
  revert H; apply relative_defined_type_mono.
  intros; apply PTree_set_In_fst_elements; auto.
Qed.

Section Consistency_Induction_Step.

Context (cenv: composite_env)
        (env: PTree.t A)
        (l: list (positive * composite))
        (i0: positive)
        (co0: composite).

Hypothesis NOT_IN_LIST: ~ In i0 (map fst l).

Hypothesis RDT_list: Forall (relative_defined_type l) (map snd (co_members co0)).

Hypothesis CENV0: PTree.get i0 cenv = Some co0.

Hypothesis IH_In_equiv: forall i, In i (map fst l) <-> In i (map fst (PTree.elements env)).

Hypothesis IH_RDT:
  forall i co a,
    PTree.get i cenv = Some co ->
    PTree.get i env = Some a ->
    Forall (relative_defined_type (PTree.elements env)) (map snd (co_members co)).

Hypothesis IH_main:
  Consistency cenv env.

Lemma NOT_IN: ~ In i0 (map fst (PTree.elements env)).
Proof.
  intros.
  rewrite <- IH_In_equiv; auto.
Qed.

Lemma RDT_PTree: Forall (relative_defined_type (PTree.elements env)) (map snd (co_members co0)).
Proof.
  intros.
  revert RDT_list; apply Forall_impl.
  intros t.
  apply relative_defined_type_mono.
  firstorder.
Qed.

Lemma establish_In_equiv:
  forall i, In i (map fst ((i0, co0) :: l)) <-> In i (map fst (PTree.elements (env_rec i0 co0 env))).
Proof.
  intros.
  specialize (IH_In_equiv i).
  rewrite PTree_In_fst_elements in IH_In_equiv |- *.
  unfold env_rec.
  rewrite <- PTree_gs_equiv.
  simpl In.
  assert (i0 = i <-> i = i0) by (split; intros; congruence).
  tauto.
Qed.

Lemma establish_RDT:
  forall i co a,
    PTree.get i cenv = Some co ->
    PTree.get i (env_rec i0 co0 env) = Some a ->
    Forall (relative_defined_type (PTree.elements (env_rec i0 co0 env))) (map snd (co_members co)).
Proof.
  pose proof RDT_PTree as RDT_PTree.
  intros i co a CENV ENV.
  unfold env_rec in ENV.
  destruct (Pos.eq_dec i i0).
  + subst i0; rewrite CENV in CENV0; inversion CENV0; subst co0; clear CENV0.
    rewrite PTree.gss in ENV.
    inversion ENV; clear a ENV H0.
    revert RDT_PTree.
    apply Forall_impl; intros t.
    apply relative_defined_type_PTree_set.
  + rewrite PTree.gso in ENV by auto.
    specialize (IH_RDT _ _ _ CENV ENV).
    revert IH_RDT.
    apply Forall_impl; intros t.
    apply relative_defined_type_PTree_set.
Qed.

Lemma establish_main:
  Consistency cenv (env_rec i0 co0 env).
Proof.
  pose proof NOT_IN as NOT_IN.
  pose proof RDT_PTree as RDT_PTree.
  intros i co a CENV ENV.
  unfold env_rec in ENV.
  destruct (Pos.eq_dec i i0).
  + subst i0; rewrite CENV in CENV0; inversion CENV0; subst co0; clear CENV0.
    rewrite PTree.gss in ENV.
    inversion ENV; clear a ENV H0.
    f_equal.
    auto.
    apply map_ext_in.
    intros (i1, t1) ?.
    f_equal.
    apply F_PTree_set; auto.
    rewrite Forall_forall in RDT_PTree; apply RDT_PTree.
    apply (in_map snd) in H; auto.
  + rewrite PTree.gso in ENV by auto.
    specialize (IH_main _ _ _ CENV ENV).
    subst a.
    f_equal.
    apply map_ext_in.
    intros (i1, t1) ?.
    f_equal.
    apply F_PTree_set; auto.
    specialize (IH_RDT _ _ _ CENV ENV).
    rewrite Forall_forall in IH_RDT; apply IH_RDT.
    apply (in_map snd) in H; auto.
Qed.

End Consistency_Induction_Step.

Lemma Consistent: forall cenv l,
  Permutation l (PTree.elements cenv) ->
  ordered_composite l ->
  Consistency cenv (Env l).
Proof.
  intros.
  assert (forall i co, In (i, co) l -> PTree.get i cenv = Some co).
  Focus 1. {
    intros.
    apply PTree.elements_complete.
    eapply Permutation_in; eauto.
  } Unfocus.
  assert (NoDup (map fst l)).
  Focus 1. {
    eapply Permutation_NoDup; [symmetry; apply Permutation_map; eassumption |].
    rewrite <- list_norepet_NoDup.
    apply PTree.elements_keys_norepet.
  } Unfocus.
  clear H.
  assert (
    (forall i, In i (map fst l) <-> In i (map fst (PTree.elements (Env l)))) /\
    (forall i co a,
      PTree.get i cenv = Some co ->
      PTree.get i (Env l) = Some a ->
      Forall (relative_defined_type (PTree.elements (Env l))) (map snd (co_members co))) /\
    Consistency cenv (Env l)); [| tauto].
  induction l as [| [i0 co0] l].
  + split; [| split]; hnf; intros.
    - simpl; tauto.
    - unfold Env in H3; simpl in H3.
      rewrite PTree.gempty in H3; inv H3.
    - unfold Env in H3; simpl in H3.
      rewrite PTree.gempty in H3; inv H3.
  + inv H0.
    rename H4 into RDT_list; specialize (IHl H6); clear H6.
    assert (CENV0: PTree.get i0 cenv = Some co0).
    Focus 1. { apply H1; left; auto. } Unfocus.
    spec IHl; [| clear H1].
    Focus 1. { intros; apply H1; right; auto. } Unfocus.
    inv H2.
    rename H1 into NOT_IN_LIST; specialize (IHl H3); clear H3.
    destruct IHl as [IH_In_equiv [IH_RDT IH_main]].
    split; [| split].
    - apply establish_In_equiv; auto.
    - eapply establish_RDT; eauto.
    - eapply establish_main; eauto.
Qed.

End type_func.

End type_func.