Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorting.
Require Import Coq.Structures.Orders.
Require Import VST.veric.Clight_base.
Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.type_induction.
Require Import VST.veric.composite_compute.
Require Import VST.veric.align_mem.
Require Import VST.veric.tycontext.
Require Import VST.veric.Cop2.

Section cs_preserve.

Context (cs_from cs_to: compspecs).

Definition test_aux (b: bool) (i: ident): bool :=
  b && match (@cenv_cs cs_from) ! i, (@cenv_cs cs_to) ! i with
       | Some co_from, Some co_to => eqb_list eqb_member (co_members co_from) (co_members co_to) && eqb_su (co_su co_from) (co_su co_to) && eqb_attr (co_attr co_from) (co_attr co_to)
       | _, _ => false
       end.

Fixpoint cs_preserve_type (coeq: PTree.t bool) (t: type): bool :=
  match t with
  | Tarray t0 _ _ => cs_preserve_type coeq t0
  | Tstruct id _ => match coeq ! id with | Some b => test_aux b id | _ => false end
  | Tunion id _ => match coeq ! id with | Some b => test_aux b id | _ => false end
  | _ => true
  end.

Fixpoint cs_preserve_members (coeq: PTree.t bool) (m: members): bool :=
  match m with
  | nil => true
  | ((_, t) :: m) => andb (cs_preserve_type coeq t) (cs_preserve_members coeq m)
  end.

Class change_composite_env: Type := {
  coeq: PTree.t bool;
  coeq_consistent:
    forall i co b,
      (@cenv_cs cs_to) ! i = Some co ->
      coeq ! i = Some b ->
      b = cs_preserve_members coeq (co_members co);
  coeq_complete:
    forall i,
      (exists co, (@cenv_cs cs_to) ! i = Some co) <->
      (exists b, coeq ! i = Some b)
}.

Definition cs_preserve_env: PTree.t bool :=
  let l := composite_reorder.rebuild_composite_elements (@cenv_cs cs_to) in
  fold_right (fun (ic: positive * composite) (T0: PTree.t bool) => let (i, co) := ic in let T := T0 in PTree.set i (cs_preserve_members T (co_members co)) T) (PTree.empty _) l.

Lemma aux1: forall T co,
  (fix fm (l : list (ident * type * bool)) : bool :=
   match l with
   | nil => true
   | (_, _, b) :: l' => b && fm l'
   end)
  (map
     (fun it0 : positive * type =>
      let (i0, t0) := it0 in
      (i0, t0,
      type_func.F (fun t : type => match t with | Tstruct _ _ | Tunion _ _ => false | _ => true end) (fun (b : bool) (_ : type) (_ : Z) (_ : attr) => b)
        (fun (b : bool) (id : ident) (_ : attr) => test_aux b id)
        (fun (b : bool) (id : ident) (_ : attr) => test_aux b id) T t0)) (co_members co)) =
  cs_preserve_members T (co_members co).
Proof.
  intros; unfold cs_preserve_members, cs_preserve_type, type_func.F.
  induction (co_members co) as [| [i t] ?].
  + auto.
  + simpl.
    f_equal; auto.
    induction t; auto.
Qed.

Lemma aux2:
  type_func.Env (fun t : type => match t with | Tstruct _ _ | Tunion _ _ => false | _ => true end) (fun (b : bool) (_ : type) (_ : Z) (_ : attr) => b)
        (fun (b : bool) (id : ident) (_ : attr) => test_aux b id)
        (fun (b : bool) (id : ident) (_ : attr) => test_aux b id)
        (fun _ : struct_or_union =>
         fix fm (l : list (ident * type * bool)) : bool :=
           match l with
           | nil => true
           | (_, _, b) :: l' => b && fm l'
           end) (composite_reorder.rebuild_composite_elements cenv_cs) =
  cs_preserve_env.
Proof.
  intros.
  unfold type_func.Env, type_func.env_rec, cs_preserve_env.
  f_equal.
  extensionality ic.
  destruct ic as [i co].
  extensionality T.
  f_equal.
  apply aux1.
Qed.

Lemma cs_preserve_env_consisent: forall (coeq: PTree.t bool),
  coeq = cs_preserve_env ->
  forall i co b,
    (@cenv_cs cs_to) ! i = Some co ->
    coeq ! i = Some b ->
    b = cs_preserve_members coeq (co_members co).
Proof.
  intros.
  pose proof @composite_reorder_consistent bool (@cenv_cs cs_to)
             (fun t : type => match t with | Tstruct _ _ | Tunion _ _ => false | _ => true end)
             (fun b _ _ _ => b)
             (fun b id _ => test_aux b id)
             (fun b id _ => test_aux b id)
             (fun _ =>
                fix fm (l: list (ident * type * bool)): bool :=
                match l with
                | nil => true
                | (_, _, b) :: l' => b && (fm l')
                end)
             (@cenv_consistent cs_to)
    as HH.
  hnf in HH.
  subst coeq0.
  rewrite aux2 in HH.
  specialize (HH _ _ b H0 H1).
  rewrite HH, aux1; auto.
Qed.

Lemma cs_preserve_completeness: forall (coeq: PTree.t bool),
  coeq = cs_preserve_env ->
  forall i,
    (exists co, (@cenv_cs cs_to) ! i = Some co) <->
    (exists b, coeq ! i = Some b).
Proof.
  intros.
  pose proof @composite_reorder_complete bool (@cenv_cs cs_to)
             (fun t : type => match t with | Tstruct _ _ | Tunion _ _ => false | _ => true end)
             (fun b _ _ _ => b)
             (fun b id _ => test_aux b id)
             (fun b id _ => test_aux b id)
             (fun _ =>
                fix fm (l: list (ident * type * bool)): bool :=
                match l with
                | nil => true
                | (_, _, b) :: l' => b && (fm l')
                end)
    as HH.
  hnf in HH.
  subst.
  rewrite aux2 in HH.
  auto.
Qed.

End cs_preserve.

Ltac make_cs_preserve cs_from cs_to :=
  let coeq0 := eval cbv in (cs_preserve_env cs_from cs_to) in
  let Hcoeq0 := constr: (eq_refl: coeq0 = cs_preserve_env cs_from cs_to) in
  let coeq0_consistent := constr: (cs_preserve_env_consisent cs_from cs_to coeq0 Hcoeq0) in
  let coeq0_complete := constr: (cs_preserve_completeness cs_from cs_to coeq0 Hcoeq0) in
  refine (  {| coeq := coeq0 ;
               coeq_consistent := coeq0_consistent;
               coeq_complete := coeq0_complete |}).

Lemma sizeof_composite_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall su (m: members),
  Forall
       (Basics.compose
          (fun t : type =>
           cs_preserve_type cs_from cs_to (coeq cs_from cs_to) t = true ->
           @sizeof (@cenv_cs cs_from) t = @sizeof (@cenv_cs cs_to) t /\
           @alignof (@cenv_cs cs_from) t = @alignof (@cenv_cs cs_to) t) snd) m ->
  true = cs_preserve_members cs_from cs_to (coeq cs_from cs_to) m ->
  sizeof_composite (@cenv_cs cs_from) su m = sizeof_composite (@cenv_cs cs_to) su m.
Proof.
  intros.
  symmetry in H0.
  destruct su; simpl; auto.
  + generalize 0 as z.
    induction H as [| [i t] ? ?]; intros; [reflexivity |].
    simpl.
    simpl in H0.
    rewrite andb_true_iff in H0.
    destruct H0.
    apply H in H0; clear H; simpl in H0; destruct H0.
    rewrite H, H0.
    apply (IHForall H2 (align z (alignof t) + sizeof t)).
  + induction H as [| [i t] ? ?]; intros; [reflexivity |].
    simpl.
    simpl in H0.
    rewrite andb_true_iff in H0.
    destruct H0.
    apply H in H0; clear H; simpl in H0; destruct H0.
    f_equal; auto.
Qed.

Lemma alignof_composite_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall (m: members),
  Forall
       (Basics.compose
          (fun t : type =>
           cs_preserve_type cs_from cs_to (coeq cs_from cs_to) t = true ->
           @sizeof (@cenv_cs cs_from) t = @sizeof (@cenv_cs cs_to) t /\
           @alignof (@cenv_cs cs_from) t = @alignof (@cenv_cs cs_to) t) snd) m ->
  true = cs_preserve_members cs_from cs_to (coeq cs_from cs_to) m ->
  alignof_composite (@cenv_cs cs_from) m = alignof_composite (@cenv_cs cs_to) m.
Proof.
  intros.
  symmetry in H0.
  induction H as [| [i t] ? ?]; intros; [reflexivity |].
  simpl.
  simpl in H0.
  rewrite andb_true_iff in H0.
  destruct H0.
  apply H in H0; clear H; simpl in H0; destruct H0.
  f_equal; auto.
Qed.

Lemma sizeof_alignof_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall (t: type),
  cs_preserve_type cs_from cs_to (coeq _ _) t = true ->
  @sizeof (@cenv_cs cs_from) t = @sizeof (@cenv_cs cs_to) t /\
  @alignof (@cenv_cs cs_from) t = @alignof (@cenv_cs cs_to) t.
Proof.
  intros t.
  type_induction t (@cenv_cs cs_to) (@cenv_consistent cs_to); intros.
  + split; reflexivity.
  + split; reflexivity.
  + split; reflexivity.
  + split; reflexivity.
  + split; reflexivity.
  + simpl.
    pose proof IH H as [? ?].
    split; f_equal; auto.
  + split; reflexivity.
  + simpl in *.
    unfold test_aux in H.
    destruct ((@cenv_cs cs_to) ! id) eqn:?H.
    - pose proof proj1 (coeq_complete _ _ _) (ex_intro _ _ H0) as [b ?H].
      rewrite H1 in H.
      destruct b; [| inv H].
      destruct ((@cenv_cs cs_from) ! id) eqn:?H; [| inv H].
      rewrite (co_consistent_sizeof (@cenv_cs cs_to) c (@cenv_consistent cs_to _ _ H0)).
      rewrite (co_consistent_sizeof (@cenv_cs cs_from) c0 (@cenv_consistent cs_from _ _ H2)).
      rewrite (co_consistent_alignof (@cenv_cs cs_to) c (@cenv_consistent cs_to _ _ H0)).
      rewrite (co_consistent_alignof (@cenv_cs cs_from) c0 (@cenv_consistent cs_from _ _ H2)).
      simpl in H.
      rewrite !andb_true_iff in H; destruct H as [[? ?] ?].
      apply eqb_list_spec in H; [| apply eqb_member_spec].
      apply eqb_su_spec in H3.
      apply eqb_attr_spec in H4.
      apply (coeq_consistent _ _ _ _ _ H0) in H1.
      rewrite H in *; rewrite H4 in  *; rewrite H3 in *; clear c0 H H0 H2 H3 H4.
      split; [f_equal; [ | f_equal] | f_equal; f_equal].
      * apply sizeof_composite_change_composite; auto.
      * apply alignof_composite_change_composite; auto.
      * apply alignof_composite_change_composite; auto.
    - destruct ((coeq cs_from cs_to) ! id) eqn:?H.
      * pose proof proj2 (coeq_complete _ _ id) (ex_intro _ b H1) as [co ?].
        congruence.
      * inv H.
  + simpl in *.
    unfold test_aux in H.
    destruct ((@cenv_cs cs_to) ! id) eqn:?H.
    - pose proof proj1 (coeq_complete _ _ _) (ex_intro _ _ H0) as [b ?H].
      rewrite H1 in H.
      destruct b; [| inv H].
      destruct ((@cenv_cs cs_from) ! id) eqn:?H; [| inv H].
      rewrite (co_consistent_sizeof (@cenv_cs cs_to) c (@cenv_consistent cs_to _ _ H0)).
      rewrite (co_consistent_sizeof (@cenv_cs cs_from) c0 (@cenv_consistent cs_from _ _ H2)).
      rewrite (co_consistent_alignof (@cenv_cs cs_to) c (@cenv_consistent cs_to _ _ H0)).
      rewrite (co_consistent_alignof (@cenv_cs cs_from) c0 (@cenv_consistent cs_from _ _ H2)).
      simpl in H.
      rewrite !andb_true_iff in H; destruct H as [[? ?] ?].
      apply eqb_list_spec in H; [| apply eqb_member_spec].
      apply eqb_su_spec in H3.
      apply eqb_attr_spec in H4.
      apply (coeq_consistent _ _ _ _ _ H0) in H1.
      rewrite H in *; rewrite H4 in  *; rewrite H3 in *; clear c0 H H0 H2 H3 H4.
      split; [f_equal; [ | f_equal] | f_equal; f_equal].
      * apply sizeof_composite_change_composite; auto.
      * apply alignof_composite_change_composite; auto.
      * apply alignof_composite_change_composite; auto.
    - destruct ((coeq cs_from cs_to) ! id) eqn:?H.
      * pose proof proj2 (coeq_complete _ _ id) (ex_intro _ b H1) as [co ?].
        congruence.
      * inv H.
Qed.

Lemma sizeof_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall (t: type),
  cs_preserve_type cs_from cs_to (coeq _ _) t = true ->
  @sizeof (@cenv_cs cs_from) t = @sizeof (@cenv_cs cs_to) t.
Proof.
  intros.
  exact (proj1 (sizeof_alignof_change_composite t H)).
Qed.

Lemma alignof_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall (t: type),
  cs_preserve_type cs_from cs_to (coeq _ _) t = true ->
  @alignof (@cenv_cs cs_from) t = @alignof (@cenv_cs cs_to) t.
Proof.
  intros.
  exact (proj2 (sizeof_alignof_change_composite t H)).
Qed.

Lemma complete_legal_cosu_type_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall (t: type),
  cs_preserve_type cs_from cs_to (coeq _ _) t = true ->
  @complete_legal_cosu_type (@cenv_cs cs_from) t = @complete_legal_cosu_type (@cenv_cs cs_to) t.
Proof.
  intros t.
  type_induction t (@cenv_cs cs_to) (@cenv_consistent cs_to); intros.
  + split; reflexivity.
  + split; reflexivity.
  + split; reflexivity.
  + split; reflexivity.
  + split; reflexivity.
  + simpl.
    apply IH; auto.
  + split; reflexivity.
  + simpl in *.
    unfold test_aux in H.
    destruct ((@cenv_cs cs_to) ! id) eqn:?H.
    - pose proof proj1 (coeq_complete _ _ _) (ex_intro _ _ H0) as [b ?H].
      rewrite H1 in H.
      destruct b; [| inv H].
      destruct ((@cenv_cs cs_from) ! id) eqn:?H; [| inv H].
      rewrite !andb_true_iff in H. destruct H as [_ [[? ?] ?]].
      apply eqb_su_spec in H3.
      rewrite H3; auto.
    - destruct ((coeq cs_from cs_to) ! id) eqn:?H.
      * pose proof proj2 (coeq_complete _ _ id) (ex_intro _ b H1) as [co ?].
        congruence.
      * inv H.
  + simpl in *.
    unfold test_aux in H.
    destruct ((@cenv_cs cs_to) ! id) eqn:?H.
    - pose proof proj1 (coeq_complete _ _ _) (ex_intro _ _ H0) as [b ?H].
      rewrite H1 in H.
      destruct b; [| inv H].
      destruct ((@cenv_cs cs_from) ! id) eqn:?H; [| inv H].
      rewrite !andb_true_iff in H. destruct H as [_ [[? ?] ?]].
      apply eqb_su_spec in H3.
      rewrite H3; auto.
    - destruct ((coeq cs_from cs_to) ! id) eqn:?H.
      * pose proof proj2 (coeq_complete _ _ id) (ex_intro _ b H1) as [co ?].
        congruence.
      * inv H.
Qed.

Lemma field_offset_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall i m,
  true = cs_preserve_members cs_from cs_to (coeq cs_from cs_to) m ->
  field_offset (@cenv_cs cs_from) i m = field_offset (@cenv_cs cs_to) i m.
Proof.
  intros.
  unfold field_offset.
  generalize 0.
  symmetry in H.
  induction m as [| [i0 t0] m]; [auto |].
  intros.
  simpl in *.
  rewrite andb_true_iff in H.
  destruct H.
  if_tac.
  + subst.
    f_equal.
    f_equal.
    apply alignof_change_composite; auto.
  + rewrite alignof_change_composite by auto.
    rewrite sizeof_change_composite by auto.
    apply IHm; auto.
Qed.

Lemma align_compatible_rec_field_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall (m: members),
  true = cs_preserve_members cs_from cs_to (coeq cs_from cs_to) m ->
  Forall
    (Basics.compose
       (fun t : type =>
          cs_preserve_type cs_from cs_to (coeq cs_from cs_to) t = true ->
          forall ofs : Z, @align_compatible_rec (@cenv_cs cs_from) t ofs <-> @align_compatible_rec (@cenv_cs cs_to) t ofs) snd)
    m ->
  forall i t,
    field_type i m = Errors.OK t ->
    forall ofs : Z, @align_compatible_rec (@cenv_cs cs_from) t ofs <-> @align_compatible_rec (@cenv_cs cs_to) t ofs.
Proof.
  intros.
  induction H0 as [| [i0 t0] m]; [inv H1 |].
  simpl in H1.
  if_tac in H1.
  + subst.
    inv H1.
    apply H0.
    simpl in H.
    symmetry in H.
    rewrite andb_true_iff in H.
    tauto.
  + apply IHForall; auto.
    simpl in H.
    symmetry in H |- *.
    rewrite andb_true_iff in H.
    tauto.
Qed.

Lemma align_compatible_rec_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall (t: type),
  cs_preserve_type cs_from cs_to (coeq _ _) t = true ->
  (forall ofs, @align_compatible_rec (@cenv_cs cs_from) t ofs <-> @align_compatible_rec (@cenv_cs cs_to) t ofs).
Proof.
  intros t.
  type_induction t (@cenv_cs cs_to) (@cenv_consistent cs_to); intros.
  + split; intros;
    inv H0; econstructor; eauto.
  + split; intros;
    inv H0; econstructor; eauto.
  + split; intros;
    inv H0; econstructor; eauto.
  + split; intros;
    inv H0; econstructor; eauto.
  + split; intros;
    inv H0; econstructor; eauto.
  + simpl.
    split; intros.
    - inv H0.
      1: inv H1.
      constructor.
      intros.
      apply IH; auto.
      rewrite <- sizeof_change_composite by auto.
      apply (H5 i); auto.
    - inv H0.
      1: inv H1.
      constructor.
      intros.
      apply IH; auto.
      rewrite sizeof_change_composite by auto.
      apply (H5 i); auto.
  + split; intros;
    inv H0; econstructor; eauto.
  + simpl in *.
    unfold test_aux in H.
    destruct ((@cenv_cs cs_to) ! id) eqn:?H.
    - pose proof proj1 (coeq_complete _ _ _) (ex_intro _ _ H0) as [b ?H].
      rewrite H1 in H.
      destruct b; [| inv H].
      destruct ((@cenv_cs cs_from) ! id) eqn:?H; [| inv H].
      rewrite !andb_true_iff in H. destruct H as [_ [[? ?] ?]].
      apply eqb_list_spec in H; [| apply eqb_member_spec].
      apply eqb_su_spec in H3.
      apply eqb_attr_spec in H4.
      apply (coeq_consistent _ _ _ _ _ H0) in H1.
      pose proof align_compatible_rec_field_change_composite _ H1 IH.
      pose proof fun i => field_offset_change_composite i _ H1.
      split; intros.
      * inv H7.
        1: inv H8.
        eapply align_compatible_rec_Tstruct; eauto.
        rewrite H2 in H10; inv H10.
        intros.
        rewrite <- H5 by eauto.
        rewrite <- H in H7, H8.
        eapply H12; eauto.
        rewrite <- H8, H.
        apply H6.
      * inv H7.
        1: inv H8.
        eapply align_compatible_rec_Tstruct; eauto.
        rewrite H0 in H10; inv H10.
        intros.
        rewrite H in H7, H8.
        rewrite H5 by eauto.
        eapply H12; eauto.
        rewrite <- H8.
        symmetry.
        apply H6.
    - destruct ((coeq cs_from cs_to) ! id) eqn:?H.
      * pose proof proj2 (coeq_complete _ _ id) (ex_intro _ b H1) as [co ?].
        congruence.
      * inv H.
  + simpl in *.
    unfold test_aux in H.
    destruct ((@cenv_cs cs_to) ! id) eqn:?H.
    - pose proof proj1 (coeq_complete _ _ _) (ex_intro _ _ H0) as [b ?H].
      rewrite H1 in H.
      destruct b; [| inv H].
      destruct ((@cenv_cs cs_from) ! id) eqn:?H; [| inv H].
      rewrite !andb_true_iff in H. destruct H as [_ [[? ?] ?]].
      apply eqb_list_spec in H; [| apply eqb_member_spec].
      apply eqb_su_spec in H3.
      apply eqb_attr_spec in H4.
      apply (coeq_consistent _ _ _ _ _ H0) in H1.
      pose proof align_compatible_rec_field_change_composite _ H1 IH.
      split; intros.
      * inv H6.
        1: inv H7.
        eapply align_compatible_rec_Tunion; eauto.
        rewrite H2 in H9; inv H9.
        intros.
        rewrite <- H5 by eauto.
        rewrite <- H in H6.
        eapply H11; eauto.
      * inv H6.
        1: inv H7.
        eapply align_compatible_rec_Tunion; eauto.
        rewrite H0 in H9; inv H9.
        intros.
        rewrite H in H6.
        rewrite H5 by eauto.
        eapply H11; eauto.
    - destruct ((coeq cs_from cs_to) ! id) eqn:?H.
      * pose proof proj2 (coeq_complete _ _ id) (ex_intro _ b H1) as [co ?].
        congruence.
      * inv H.
Qed.
