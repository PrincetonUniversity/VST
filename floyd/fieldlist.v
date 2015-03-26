Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.

Arguments align !n !amount / .
Arguments Z.max !n !m / .

Definition in_members i (m: members): Prop :=
  In i (map fst m).

Definition field_type2 i m :=
  match field_type i m with
  | Errors.OK t => t
  | _ => Tvoid
  end.

Definition field_offset2 env i m :=
  match field_offset env i m with
  | Errors.OK ofs => ofs
  | _ => 0
  end.

Definition compute_in_members id (m: members): bool :=
  id_in_list id (map fst m).
                                                                      
Definition members_no_replicate (m: members) : bool :=
  compute_list_norepet (map fst m).

Lemma compute_in_members_true_iff: forall i m, compute_in_members i m = true <-> in_members i m.
Proof.
  intros.
  unfold compute_in_members.
  destruct (id_in_list i (map fst m)) eqn:HH; 
  [apply id_in_list_true in HH | apply id_in_list_false in HH].
  + unfold in_members.
    tauto.
  + unfold in_members; split; [congruence | tauto].
Qed.

Lemma compute_in_members_false_iff: forall i m,
  compute_in_members i m = false <-> ~ in_members i m.
Proof.
  intros.
  pose proof compute_in_members_true_iff i m.
  rewrite <- H; clear H.
  destruct (compute_in_members i m); split; congruence.
Qed.

Ltac destruct_in_members i m :=
  let H := fresh "H" in
  destruct (compute_in_members i m) eqn:H;
    [apply compute_in_members_true_iff in H |
     apply compute_in_members_false_iff in H].

Lemma in_members_dec: forall i m, {in_members i m} + {~ in_members i m}.
Proof.
  intros.
  destruct_in_members i m; [left | right]; auto.
Qed.

Lemma in_members_field_type2: forall i m,
  in_members i m ->
  In (i, field_type2 i m) m.
Proof.
  intros.
  unfold field_type2.
  induction m as [|[i0 t0] m].
  + inversion H.
  + unfold in_members in H; simpl in H.
    destruct (ident_eq i0 i).
    - subst.
      simpl.
      if_tac; [| congruence].
      left. auto.
    - simpl.
      right.
      destruct H; [congruence |].
      specialize (IHm H).
      if_tac; [congruence |].
      exact IHm.
Qed.
 
Lemma field_offset_field_type_match: forall cenv i m,
  match field_offset cenv i m, field_type i m with
  | Errors.OK _, Errors.OK _ => True
  | Errors.Error _, Errors.Error _ => True
  | _, _ => False
  end.
Proof.
  intros.
  unfold field_offset.
  remember 0 as pos; clear Heqpos.
  revert pos; induction m as [| [? ?] ?]; intros.
  + simpl. auto.
  + simpl. destruct (ident_eq i i0) eqn:HH.
    - auto.
    - apply IHm.
Defined.

Lemma field_type_in_members: forall i m,
  match field_type i m with
  | Errors.Error _ => ~ in_members i m
  | _ => in_members i m
  end.
Proof.
  intros.
  unfold in_members.
  induction m as [| [i0 t0] m].
  + simpl; tauto.
  + simpl.
    destruct (ident_eq i i0).
    - left; subst; auto.
    - if_tac.
      * right; auto.
      * intro HH; destruct HH; [congruence | tauto].
Qed.

Section COMPOSITE_ENV.
Context {cs: compspecs}.

Ltac solve_field_offset_type i m :=
  let H := fresh "H" in 
  let Hty := fresh "H" in 
  let Hofs := fresh "H" in 
  let t := fresh "t" in
  let ofs := fresh "ofs" in
  pose proof field_offset_field_type_match cenv_cs i m;
  destruct (field_offset cenv_cs i m) as [ofs|?] eqn:Hofs, (field_type i m) as [t|?] eqn:Hty;
    [clear H | inversion H | inversion H | clear H].

Lemma complete_type_field_type2: forall id i co,
  cenv_cs ! id = Some co ->
  in_members i (co_members co) ->
  complete_type cenv_cs (field_type2 i (co_members co)) = true.
Proof.
  intros.
  apply in_members_field_type2 in H0.
  eapply complete_member; eauto.
  apply co_consistent_complete.
  exact (cenv_consistent_cs id co H).
Qed.

Lemma field_offset2_aligned: forall i m,
  (alignof cenv_cs (field_type2 i m) | field_offset2 cenv_cs i m).
Proof.
  intros.
  unfold field_type2, field_offset2.
  solve_field_offset_type i m.
  + eapply field_offset_aligned; eauto.
  + apply Z.divide_0_r.
Qed.

Lemma alignof_composite_hd_divide: forall i t m, (alignof cenv_cs t | alignof_composite cenv_cs ((i, t) :: m)).
Proof.
  intros.
  destruct (alignof_two_p cenv_cs t) as [N ?].
  destruct (alignof_composite_two_p cenv_cs ((i, t) :: m)) as [M ?].
  assert (alignof cenv_cs t <= alignof_composite cenv_cs ((i,t)::m)) by (apply Z.le_max_l).
  rewrite H in *.
  rewrite H0 in *.
  exact (power_nat_divide N M H1).
Qed.

Lemma alignof_composite_tl_divide: forall i t m, (alignof_composite cenv_cs m | alignof_composite cenv_cs ((i, t) :: m)).
Proof.
  intros.
  destruct (alignof_composite_two_p cenv_cs m) as [N ?].
  destruct (alignof_composite_two_p cenv_cs ((i, t) :: m)) as [M ?].
  assert (alignof_composite cenv_cs m <= alignof_composite cenv_cs ((i, t) :: m)) by (apply Z.le_max_r).
  rewrite H in *.
  rewrite H0 in *.
  exact (power_nat_divide N M H1).
Qed.

Lemma alignof_field_type2: forall i m,
  in_members i m ->
  (alignof cenv_cs (field_type2 i m) | alignof_composite cenv_cs m).
Proof.
  intros.
  unfold field_type2.
  induction m as [| [i0 t0] m].
  + inversion H.
  + unfold in_members in H; simpl in H.
    simpl field_type.
    if_tac.
    - apply alignof_composite_hd_divide.
    - eapply Zdivide_trans.
      * apply IHm.
        destruct H; [congruence | auto].
      * apply alignof_composite_tl_divide.
Qed.

Lemma field_offset2_in_range: forall i m,
  in_members i m ->
  0 <= field_offset2 cenv_cs i m /\ field_offset2 cenv_cs i m + sizeof cenv_cs (field_type2 i m) <= sizeof_struct cenv_cs 0 m.
Proof.
  intros.
  unfold field_offset2, field_type2.
  solve_field_offset_type i m.
  + eapply field_offset_in_range; eauto.
  + pose proof field_type_in_members i m.
    rewrite H1 in H0.
    tauto.
Qed.

Lemma sizeof_union_in_members: forall i m,
  in_members i m ->
  sizeof cenv_cs (field_type2 i m) <= sizeof_union cenv_cs m.
(* field_offset2_in_range union's version *)
Proof.
  intros.
  unfold in_members in H.
  unfold field_type2.
  induction m as [|[i0 t0] m].
  + inversion H.
  + simpl.
    destruct (ident_eq i i0).
    - apply Z.le_max_l.
    - simpl in H; destruct H; [congruence |].
     specialize (IHm H).
     pose proof Z.le_max_r (sizeof cenv_cs t0) (sizeof_union cenv_cs m).
     omega.
Qed.

End COMPOSITE_ENV.

(************************************************

Lemmas about fieldlist_app

************************************************)
(*
Lemma fieldlist_app_Fnil: forall f, fieldlist_app f Fnil = f.
Proof.
  intros.
  induction f.
  + reflexivity.
  + simpl. rewrite IHf. reflexivity.
Defined.

Lemma fieldlist_app_Fcons: forall m1 i t f2, fieldlist_app m1 (Fcons i t f2) = fieldlist_app (fieldlist_app m1 (Fcons i t Fnil)) f2.
Proof.
  intros.
  induction m1.
  + reflexivity.
  + simpl.
    rewrite IHm1.
    reflexivity.
Defined.

Lemma id_in_members_app: forall i (m1 m2: members),
  id_in_members i (m1 ++ m2) = (id_in_members i m1 || id_in_members i m2)%bool.
Proof.
  intros.
  induction m1 as [| [? ?] ?]; simpl.
  + reflexivity.
  + if_tac.
    - reflexivity.
    - exact IHm1.
Qed.

Lemma members_no_replicate_fact:
  forall m1 m2 i, members_no_replicate (app m1 m2) = true ->
  isOK (field_type i m1) = true -> isOK (field_type i m2) = true -> False.
Proof.
  intros.
  induction m1 as [| [? ?] ?].
  + inversion H0.
  + unfold members_no_replicate in H; simpl in H0, H.
    if_tac in H0.
    - rewrite members_app_field_type_isOK in H.
      rewrite negb_true_iff, orb_false_iff in H.
      destruct H as [_ ?].
      subst.
      congruence.
    - destruct H as [_ ?].
      apply IHm1; auto.
Qed.

(****************************************************************

field_type_hd, field_type_mid, field_offset_hd, field_offset_mid

****************************************************************)

Lemma field_type_hd: forall i t f, field_type i (Fcons i t f) = Errors.OK t.
Proof.
  intros.
  simpl.
  if_tac; [reflexivity | congruence].
Defined.

Lemma field_type_mid: forall i t f' f, fieldlist_no_replicate (fieldlist_app f' (Fcons i t f)) = true -> field_type i (fieldlist_app f' (Fcons i t f)) = Errors.OK t.
Proof.
  intros.
  pose proof field_type_hd i t f.
  assert (isOK (field_type i (Fcons i t f)) = true) by (simpl; if_tac; [| congruence]; reflexivity).
  remember (Fcons i t f) as f''; clear Heqf'' f.
  pose proof (fun HH => fieldlist_no_replicate_fact _ _ _ H HH H1).
  clear H1.
  induction f'.
  + exact H0.
  + simpl in *.
    destruct (ident_eq i i0); [simpl in H2; congruence|].
    apply andb_true_iff in H; destruct H as [_ ?]. 
    exact (IHf' H H2).
Defined.

Lemma field_offset_hd: forall i t f, field_offset i (Fcons i t f) = Errors.OK 0.
Proof.
  intros.
  unfold field_offset.
  simpl.
  if_tac; [rewrite (align_0 _ (alignof_pos _)); reflexivity | congruence].
Defined.

Lemma field_offset_mid: forall i0 t0 i1 t1 f' f ofs, fieldlist_no_replicate (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f))) = true -> field_offset i1 (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f))) = Errors.OK ofs -> field_offset i0 (fieldlist_app f' (Fcons i1 t1 (Fcons i0 t0 f))) = Errors.OK (align (ofs + sizeof t1) (alignof t0)).
Proof.
  intros.
  unfold field_offset in *.
  remember 0 as pos; clear Heqpos.
  revert pos H0; induction f'; intros.
  + simpl in *.
    if_tac.
    - if_tac in H; try congruence. inversion H.
    - if_tac in H; try congruence; clear H1.
      if_tac in H0; try congruence; clear H1.
      if_tac; try congruence.
  + simpl in *.
    apply andb_true_iff in H.
    destruct H.
    destruct (isOK (field_type i (Fcons i1 t1 (Fcons i0 t0 f)))) eqn:H';
      [rewrite fieldlist_app_field_type_isOK in H; rewrite H' in H;
       destruct (isOK (field_type i f')); inversion H|].
    simpl in H'.
    if_tac in H'; try solve [inversion H'].
    if_tac in H'; try solve [inversion H'].
    if_tac; try congruence.
    if_tac in H0; try congruence.
    apply (IHf' H1), H0.
Defined.

(****************************************************************

Other lemmas

****************************************************************)

Lemma field_offset_in_range': forall sid fld a fid ty,
  field_type fid fld = Errors.OK ty ->
  sizeof ty <= sizeof (Tunion sid fld a).
Proof.
  intros.
  simpl.
  pose proof alignof_pos (Tunion sid fld a).
  assert (sizeof_union fld <= align (sizeof_union fld) (alignof (Tunion sid fld a)))
    by (apply align_le; omega).
  cut (sizeof ty <= sizeof_union fld); [simpl in *; omega |].
  clear -H.
  induction fld.
  + inversion H.
  + simpl in *. if_tac in H.
    - inversion H.
      apply Z.le_max_l.
    - apply Zmax_bound_r, IHfld, H.
Qed.

Lemma eqb_fieldlist_true: forall m1 m2, eqb_fieldlist m1 m2 = true -> m1 = m2.
Proof.
  intros.
  revert m2 H; induction m1; intros; destruct m2; simpl in *.
  + reflexivity.
  + inversion H.
  + inversion H.
  + apply andb_true_iff in H.
    destruct H.
    apply andb_true_iff in H0.
    destruct H0.
    apply IHm1 in H1.
    apply eqb_type_true in H0.
    apply eqb_ident_spec in H.
    subst; reflexivity.
Qed.


*)