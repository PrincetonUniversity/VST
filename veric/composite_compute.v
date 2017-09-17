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

(* Aux: composite_env's PTree members reordering *)

Definition PTree_get_list {A: Type} (i: positive) (T: PTree.t (list A)): list A :=
  match PTree.get i T with
  | Some l => l
  | None => nil
  end.

Definition PTree_set_cons {A: Type} (i: positive) (a: A) (T: PTree.t (list A)) :=
  PTree.set i (a :: PTree_get_list i T) T.

Definition rebuild_composite_tree (env: composite_env): PTree.t (list (ident * composite)) :=
  fold_right (fun ic => PTree_set_cons (Pos.of_succ_nat (co_rank (snd ic))) ic) (PTree.empty _) (PTree.elements env).

Definition max_rank_composite (env: composite_env): nat :=
  fold_right (fun ic => max (co_rank (snd ic))) O (PTree.elements env).

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