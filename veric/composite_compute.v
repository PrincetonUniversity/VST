Require Import Coq.Sorting.Permutation.
Require Import VST.veric.base.
Require Import VST.veric.Clight_lemmas.

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

Fixpoint Env (l: list (positive * composite)): PTree.t A :=
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
  induction t; auto.
  + simpl in H |- *.
    apply PTree_set_In_fst_elements; auto.
  + simpl in H |- *.
    apply PTree_set_In_fst_elements; auto.
Qed.

Lemma aux_induction_step: forall cenv env i0 co0,
  ~ In i0 (map fst (PTree.elements env)) ->
  Forall (relative_defined_type (PTree.elements env)) (map snd (co_members co0)) ->
  PTree.get i0 cenv = Some co0 ->
  (forall i co a,
      PTree.get i cenv = Some co ->
      PTree.get i env = Some a ->
      Forall (relative_defined_type (PTree.elements env)) (map snd (co_members co))) ->
  (forall i co a,
      PTree.get i cenv = Some co ->
      PTree.get i (env_rec i0 co0 env) = Some a ->
      Forall (relative_defined_type (PTree.elements (env_rec i0 co0 env))) (map snd (co_members co))).
Proof.
  intros ? ? i0 co0 NOT_IN RDT CENV0 IH_RDT.
  intros i co a CENV ENV.
  unfold env_rec in ENV.
  destruct (Pos.eq_dec i i0).
  + subst i0; rewrite CENV in CENV0; inversion CENV0; subst co0; clear CENV0.
    rewrite PTree.gss in ENV.
    inversion ENV; clear a ENV H0.
    revert RDT.
    apply Forall_impl; intros t.
    apply relative_defined_type_PTree_set.
  + rewrite PTree.gso in ENV by auto.
    specialize (IH_RDT _ _ _ CENV ENV).
    revert IH_RDT.
    apply Forall_impl; intros t.
    apply relative_defined_type_PTree_set.
Qed.

Lemma consistent_induction_step: forall cenv env i0 co0,
  ~ In i0 (map fst (PTree.elements env)) ->
  Forall (relative_defined_type (PTree.elements env)) (map snd (co_members co0)) ->
  PTree.get i0 cenv = Some co0 ->
  (forall i co a,
      PTree.get i cenv = Some co ->
      PTree.get i env = Some a ->
      Forall (relative_defined_type (PTree.elements env)) (map snd (co_members co))) ->
  Consistency cenv env ->
  Consistency cenv (env_rec i0 co0 env).
Proof.
  intros ? ? i0 co0 NOT_IN RDT CENV0 IH_RDT IH_main.
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
    rewrite Forall_forall in RDT; apply RDT.
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

Lemma Consistent: forall cenv l,
  Permutation l (PTree.elements cenv) ->
  ordered_composite l ->
  Consistency cenv (Env l).
Proof.
  intros.
  assert (
    (forall i co a,
      PTree.get i cenv = Some co ->
      PTree.get i (Env l) = Some a ->
      Forall (relative_defined_type (PTree.elements (Env l))) (map snd (co_members co))) /\
    Consistency cenv (Env l)); [| tauto].
  induction l as [| [i0 co0] l].
  + split; hnf; intros.
    - unfold Env in H2; simpl in H2.
      rewrite PTree.gempty in H2; inv H2.
    - unfold Env in H2; simpl in H2.
      rewrite PTree.gempty in H2; inv H2.
  + split.
    - apply aux_induction_step; admit.
    - apply consistent_induction_step; admit.
Admitted.