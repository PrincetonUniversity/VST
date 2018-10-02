Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorting.
Require Import Coq.Structures.Orders.
Require Import VST.veric.base.

Require Import compcert.cfrontend.Ctypes. 

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

Inductive ordered_composite: list (positive * composite) -> Prop :=
| ordered_composite_nil: ordered_composite nil
| ordered_composite_cons: forall i co l,
    Forall (relative_defined_type l) (map snd (co_members co)) ->
    ordered_composite l ->
    ordered_composite ((i, co) :: l).

Module composite_reorder.

(* Use merge sort instead *)
(* Sort rank from higher to lower *)
Module CompositeRankOrder <: TotalLeBool.
  Definition t := (positive * composite)%type.
  Definition leb (x y: t) := Nat.leb (co_rank (snd y)) (co_rank (snd x)).

  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    intros.
    unfold leb.
    rewrite !Nat.leb_le.
    omega.
  Qed.

  Theorem leb_trans: Transitive (fun x y => is_true (leb x y)).
  Proof.
    hnf; intros; unfold leb, is_true in *.
    rewrite !Nat.leb_le in *.
    omega.
  Qed.

End CompositeRankOrder.

Module CompositeRankSort := Sort CompositeRankOrder.

Section composite_reorder.

Context (cenv: composite_env)
        (cenv_consistent: composite_env_consistent cenv).

Definition rebuild_composite_elements := CompositeRankSort.sort (PTree.elements cenv).

Inductive ordered_and_complete: list (positive * composite) -> Prop :=
| ordered_and_complete_nil: ordered_and_complete nil
| ordered_and_complete_cons: forall i co l,
    (forall i' co',
        cenv ! i' = Some co' ->
        (co_rank co' < co_rank co)%nat ->
        In (i', co') l) ->
    ordered_and_complete l ->
    ordered_and_complete ((i, co) :: l).

Theorem RCT_Permutation: Permutation rebuild_composite_elements (PTree.elements cenv).
Proof.
  symmetry.
  apply CompositeRankSort.Permuted_sort.
Qed.

Lemma RCT_ordered_and_complete: ordered_and_complete rebuild_composite_elements.
Proof.
  pose proof RCT_Permutation.
  assert (forall i co, cenv ! i = Some co -> In (i, co) rebuild_composite_elements).
  {
    intros.
    eapply Permutation_in.
    + symmetry; apply RCT_Permutation.
    + apply PTree.elements_correct; auto.
  } 
  clear H.
  pose proof CompositeRankSort.StronglySorted_sort (PTree.elements cenv) CompositeRankOrder.leb_trans.
  pose proof app_nil_l rebuild_composite_elements.
  unfold rebuild_composite_elements in *.
  set (l := (CompositeRankSort.sort (PTree.elements cenv))) in H1 at 1 |- *.
  revert H1; generalize (@nil (positive * composite)).
  clearbody l.
  induction l; intros.
  + constructor.
  + specialize (IHl (l0 ++ a :: nil)).
    rewrite <- app_assoc in IHl.
    specialize (IHl H1).
    destruct a as [i co]; constructor; auto.
    intros.
    apply H0 in H2.
    rewrite <- H1 in H2, H.
    clear - H2 H3 H.
    induction l0.
    - destruct H2; auto.
      exfalso; inv H0.
      omega.
    - inv H.
      destruct H2.
      * exfalso.
        subst.
        rewrite Forall_forall in H5.
        specialize (H5 (i, co)).
        rewrite in_app in H5.
        specialize (H5 (or_intror (or_introl eq_refl))).
        unfold is_true in H5.
        rewrite Nat.leb_le in H5; simpl in H5.
        omega.
      * apply IHl0; auto.
Qed.

Theorem RCT_ordered: ordered_composite rebuild_composite_elements.
Proof.
  pose proof RCT_ordered_and_complete.
  assert (forall i co, In (i, co) rebuild_composite_elements -> complete_members cenv (co_members co) = true /\ co_rank co = rank_members cenv (co_members co)).
  {
    intros.
    eapply Permutation_in in H0; [| exact RCT_Permutation].
    apply PTree.elements_complete in H0; auto.
    split.
    + apply co_consistent_complete.
      eapply cenv_consistent; eauto.
    + apply co_consistent_rank.
      eapply cenv_consistent; eauto.
  }
  induction H.
  + constructor.
  + specialize (IHordered_and_complete (fun i co HH => H0 i co (or_intror HH))).
    constructor; auto.
    clear IHordered_and_complete H1.
    specialize (H0 _ _ (or_introl eq_refl)).
    assert (rank_members cenv (co_members co) <= co_rank co)%nat by omega.
    destruct H0 as [? _].
    induction (co_members co) as [| [i0 t0] ?].
    - constructor.
    - simpl in H0; rewrite andb_true_iff in H0; destruct H0.
      simpl in H1; pose proof Max.max_lub_r _ _ _ H1.
      apply Max.max_lub_l in H1.
      constructor; auto; clear IHm H2 H3.
      simpl.
      induction t0; try solve [simpl; auto].
      * (* array *)
        spec IHt0; auto.
        spec IHt0; [simpl in H1; omega |].
        auto.
      * (* struct *)
        simpl in H0, H1 |- *.
        destruct (cenv ! i1) eqn:?H; [| inv H0].
        specialize (H _ _ H2).
        spec H; [omega |].
        apply (in_map fst) in H; auto.
      * (* union *)
        simpl in H0, H1 |- *.
        destruct (cenv ! i1) eqn:?H; [| inv H0].
        specialize (H _ _ H2).
        spec H; [omega |].
        apply (in_map fst) in H; auto.
Qed.

End composite_reorder.

End composite_reorder.

Module type_func.
Section type_func.

Context {A: Type}
        (f_default: type -> A)
        (f_array: A -> type -> Z -> attr -> A)
        (f_struct: A -> ident -> attr -> A)
        (f_union: A -> ident -> attr -> A)
        (f_member: struct_or_union -> list (ident * type * A) -> A).

Fixpoint F (env: PTree.t A) (t: type): A :=
  match t with
  | Tarray t n a => f_array (F env t) t n a
  | Tstruct id a =>
      match env ! id with
      | Some v => f_struct v id a
      | None => f_default t
      end
  | Tunion id a =>
      match env ! id with
      | Some v => f_union v id a
      | None => f_default t
      end
  | _ => f_default t
  end.

Definition Complete (cenv: composite_env) (env: PTree.t A): Prop :=
  forall i,
    (exists co, PTree.get i cenv = Some co) <->
    (exists a, PTree.get i env = Some a).

Definition Consistent (cenv: composite_env) (env: PTree.t A): Prop :=
  forall i co a,
    PTree.get i cenv = Some co ->
    PTree.get i env = Some a ->
    a = f_member (co_su co) (map
                              (fun it0: positive * type =>
                                 let (i0, t0) := it0 in
                                 (i0, t0, F env t0))
                              (co_members co)).

Definition env_rec (i: positive) (co: composite) (env: PTree.t A): PTree.t A :=
  PTree.set i
    (f_member (co_su co) (map
                              (fun it0: positive * type =>
                                 let (i0, t0) := it0 in (i0, t0, F env t0))
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
  Consistent cenv env.

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
  Consistent cenv (env_rec i0 co0 env).
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

Lemma Consistency: forall cenv l,
  Permutation l (PTree.elements cenv) ->
  ordered_composite l ->
  Consistent cenv (Env l).
Proof.
  intros.
  assert (forall i co, In (i, co) l -> PTree.get i cenv = Some co).
  {
    intros.
    apply PTree.elements_complete.
    eapply Permutation_in; eauto.
  }
  assert (NoDup (map fst l)).
  {
    eapply Permutation_NoDup; [symmetry; apply Permutation_map; eassumption |].
    rewrite <- list_norepet_NoDup.
    apply PTree.elements_keys_norepet.
  }
  clear H.
  assert (
    (forall i, In i (map fst l) <-> In i (map fst (PTree.elements (Env l)))) /\
    (forall i co a,
      PTree.get i cenv = Some co ->
      PTree.get i (Env l) = Some a ->
      Forall (relative_defined_type (PTree.elements (Env l))) (map snd (co_members co))) /\
    Consistent cenv (Env l)); [| tauto].
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
    { apply H1; left; auto. }
    spec IHl; [| clear H1].
    { intros; apply H1; right; auto. } 
    inv H2.
    rename H1 into NOT_IN_LIST; specialize (IHl H3); clear H3.
    destruct IHl as [IH_In_equiv [IH_RDT IH_main]].
    split; [| split].
    - apply establish_In_equiv; auto.
    - eapply establish_RDT; eauto.
    - eapply establish_main; eauto.
Qed.

Lemma Completeness: forall cenv l,
  Permutation l (PTree.elements cenv) ->
  Complete cenv (Env l).
Proof.
  intros.
  intro.
  rewrite <- !PTree_In_fst_elements.
  pose proof PTree.elements_keys_norepet cenv.
  rewrite list_norepet_NoDup in H0.
  rewrite <- H in H0 |- *; clear H.
  induction l.
  + simpl; tauto.
  + destruct a as [i0 co0].
    inv H0.
    specialize (IHl H3).
    simpl.
    unfold env_rec.
    rewrite PTree_In_fst_elements, <- PTree_gs_equiv, <- PTree_In_fst_elements.
    assert (i = i0 <-> i0 = i) by (split; intros; congruence).
    tauto.
Qed.

End type_func.

End type_func.

Corollary composite_reorder_consistent {A: Type}:
  forall cenv f_default f_array f_struct f_union f_members,
    composite_env_consistent cenv ->
    type_func.Consistent f_default f_array f_struct f_union f_members cenv (@type_func.Env A f_default f_array f_struct f_union f_members (composite_reorder.rebuild_composite_elements cenv)).
Proof.
  intros.
  apply type_func.Consistency.
  + apply composite_reorder.RCT_Permutation.
  + apply composite_reorder.RCT_ordered; auto.
Qed.

Corollary composite_reorder_complete {A: Type}:
  forall cenv f_default f_array f_struct f_union f_members,
    type_func.Complete cenv (@type_func.Env A f_default f_array f_struct f_union f_members (composite_reorder.rebuild_composite_elements cenv)).
Proof.
  intros.
  apply type_func.Completeness.
  apply composite_reorder.RCT_Permutation.
Qed.

Section cuof.

Context (cenv: composite_env).

Fixpoint complete_legal_cosu_type t :=
  match t with
  | Tarray t' _ _ => complete_legal_cosu_type t'
  | Tstruct id _ => match cenv ! id with
                    | Some co => match co_su co with
                                 | Struct => true
                                 | Union => false
                                 end
                    | _ => false
                    end
  | Tunion id _ => match cenv ! id with
                   | Some co => match co_su co with
                                | Struct => false
                                | Union => true
                                end
                   | _ => false
                   end
  | Tfunction _ _ _
  | Tvoid => false
  | _ => true
  end.

Fixpoint composite_complete_legal_cosu_type (m: members): bool :=
  match m with
  | nil => true
  | (_, t) :: m' => complete_legal_cosu_type t && composite_complete_legal_cosu_type m'
  end.

Definition composite_env_complete_legal_cosu_type: Prop :=
  forall (id : positive) (co : composite),
    cenv ! id = Some co -> composite_complete_legal_cosu_type (co_members co) = true.
  
End cuof.

Lemma complete_legal_cosu_type_complete_type: forall cenv: composite_env,
  forall t,
    complete_legal_cosu_type cenv t = true ->
    complete_type cenv t = true.
Proof.
  intros.
  induction t; auto.
  + simpl in *.
    destruct (cenv ! i); auto.
  + simpl in *.
    destruct (cenv ! i); auto.
Qed.

