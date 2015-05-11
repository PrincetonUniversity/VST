Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.

Arguments align !n !amount / .
Arguments Z.max !n !m / .

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

Fixpoint field_offset_next_rec env i m ofs sz :=
  match m with
  | nil => 0
  | (i0, t0) :: m0 =>
    match m0 with
    | nil => sz
    | (_, t1) :: _ =>
      if ident_eq i i0
      then align (ofs + sizeof env t0) (alignof env t1)
      else field_offset_next_rec env i m0 (align (ofs + sizeof env t0) (alignof env t1)) sz
    end
  end.

Definition field_offset_next env i m sz := field_offset_next_rec env i m 0 sz.

Definition compute_in_members id (m: members): bool :=
  id_in_list id (map fst m).
                                                                      
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

Lemma complete_type_field_type2: forall id i,
  in_members i (co_members (get_co id)) ->
  complete_type cenv_cs (field_type2 i (co_members (get_co id))) = true.
Proof.
  unfold get_co.
  intros.
  destruct (cenv_cs ! id) as [co |] eqn:CO.
  + apply in_members_field_type2 in H.
    eapply complete_member; eauto.
    apply co_consistent_complete.
    exact (cenv_consistent_cs id co CO).
  + inversion H.
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

Lemma alignof_field_type2_divide_alignof: forall i m,
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

(* if sizeof Tvoid = 0, this lemma can be nicer. *)
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

(* if sizeof Tvoid = 0, this lemma can be nicer. *)
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

(* if sizeof Tvoid = 0, this lemma can be nicer. *)
Lemma field_offset2_no_overlap:
  forall i1 i2 m,
  i1 <> i2 ->
  in_members i1 m ->
  in_members i2 m ->
  field_offset2 cenv_cs i1 m + sizeof cenv_cs (field_type2 i1 m) <= field_offset2 cenv_cs i2 m \/
  field_offset2 cenv_cs i2 m + sizeof cenv_cs (field_type2 i2 m) <= field_offset2 cenv_cs i1 m.
Proof.
  intros.
  unfold field_offset2, field_type2.
  pose proof field_type_in_members i1 m.
  pose proof field_type_in_members i2 m.
  solve_field_offset_type i1 m;
  solve_field_offset_type i2 m; try tauto.
  eapply field_offset_no_overlap; eauto.
Qed.

Lemma not_in_members_field_type2: forall i m,
  ~ in_members i m ->
  field_type2 i m = Tvoid.
Proof.
  unfold in_members, field_type2.
  intros.
  induction m as [| [i0 t0] m].
  + reflexivity.
  + simpl in H.
    simpl.
    destruct (ident_eq i i0) as [HH | HH]; pose proof (@eq_sym ident i i0); tauto.
Qed.

Lemma not_in_members_field_offset2: forall i m,
  ~ in_members i m ->
  field_offset2 cenv_cs i m = 0.
Proof.
  unfold in_members, field_offset2, field_offset.
  intros.
  generalize 0 at 1.
  induction m as [| [i0 t0] m]; intros.
  + reflexivity.
  + simpl in H.
    simpl.
    destruct (ident_eq i i0) as [HH | HH]; pose proof (@eq_sym ident i i0); [tauto |].
    apply IHm. tauto.
Qed.

Lemma field_offset_next_in_range: forall i m sz,
  in_members i m ->
  sizeof_struct cenv_cs 0 m <= sz ->
  field_offset2 cenv_cs i m + sizeof cenv_cs (field_type2 i m) <=
  field_offset_next cenv_cs i m sz <= sz.
Proof.
  intros.
  destruct m as [| [i0 t0] m]; [inversion H |].
  unfold field_offset2, field_offset, field_offset_next, field_type2.
  pattern 0 at 3 4; replace 0 with (align 0 (alignof cenv_cs t0)) by (apply align_0, alignof_pos).
  match goal with
  | |- ?A => assert (A /\
                     match field_offset_rec cenv_cs i ((i0, t0) :: m) 0 with
                     | Errors.OK _ => True
                     | _ => False
                     end /\
                     match field_type i ((i0, t0) :: m) with
                     | Errors.OK _ => True
                     | _ => False
                     end); [| tauto]
  end.
  revert i0 t0 H H0; generalize 0; induction m as [| [i1 t1] m]; intros.
  + destruct (ident_eq i i0); [| destruct H; simpl in H; try congruence; tauto].
    subst; simpl.
    if_tac; [| congruence].
    split; [| split]; auto.
    simpl in H0.
    omega.
  + remember ((i1, t1) :: m) as m0. simpl in H0 |- *. subst m0.
    destruct (ident_eq i i0).
    - split; [| split]; auto.
      split.
      * apply align_le, alignof_pos.
      * pose proof sizeof_struct_incr cenv_cs m (align (align z (alignof cenv_cs t0) + sizeof cenv_cs t0)
            (alignof cenv_cs t1) + sizeof cenv_cs t1).
        pose proof sizeof_pos cenv_cs t1.
        simpl in H0; omega.
    - destruct H as [H | H]; [simpl in H; congruence |].
      specialize (IHm (align z (alignof cenv_cs t0) + sizeof cenv_cs t0) i1 t1 H H0).
      destruct (field_offset_rec cenv_cs i ((i1, t1) :: m) (align z (alignof cenv_cs t0) + sizeof cenv_cs t0)),
               (field_type i ((i1, t1) :: m));
      try tauto.
Qed.

Lemma members_no_replicate_ind: forall m,
  (members_no_replicate m = true) <->
  match m with
  | nil => True
  | (i0, _) :: m0 => ~ in_members i0 m0 /\ members_no_replicate m0 = true
  end.
Proof.
  intros.
  unfold members_no_replicate.
  destruct m as [| [i t] m]; simpl.
  + assert (true = true) by auto; tauto.
  + destruct (id_in_list i (map fst m)) eqn:HH.
    - apply id_in_list_true in HH.
      assert (~ false = true) by congruence; tauto.
    - apply id_in_list_false in HH.
      tauto.
Defined.

Lemma map_members_ext: forall A (f f':ident * type -> A) (m: members),
  members_no_replicate m = true ->
  (forall i, in_members i m -> f (i, field_type2 i m) = f' (i, field_type2 i m)) ->
  map f m = map f' m.
Proof.
  intros.
  induction m as [| (i0, t0) m].
  + reflexivity.
  + simpl.
    rewrite members_no_replicate_ind in H.
    f_equal.
    - specialize (H0 i0).
      unfold field_type2, in_members in H0.
      simpl in H0; if_tac in H0; [| congruence].
      apply H0; auto.
    - apply IHm; [tauto |].
      intros.
      specialize (H0 i).
      unfold field_type2, in_members in H0.
      simpl in H0; if_tac in H0; [subst; tauto |].
      apply H0; auto.
Defined.

Lemma in_members_tail_no_replicate: forall i i0 t0 m,
  members_no_replicate ((i0, t0) :: m) = true ->
  in_members i m ->
  i <> i0.
Proof.
  intros.
  rewrite members_no_replicate_ind in H.
  intro.
  subst; tauto.
Defined.

Lemma neq_field_offset_rec_cons: forall env i i0 t0 m z,
  i <> i0 ->
  field_offset_rec env i ((i0, t0) :: m) z =
  field_offset_rec env i m (align z (alignof env t0) + sizeof env t0).
Proof.
  intros.
  simpl.
  if_tac; [congruence |].
  auto.
Qed.

Lemma neq_field_offset_next_rec_cons: forall env i i0 t0 i1 t1 m z sz,
  i <> i0 ->
  field_offset_next_rec env i ((i0, t0) :: (i1, t1) :: m) z sz =
  field_offset_next_rec env i ((i1, t1) :: m) (align (z + sizeof env t0) (alignof env t1)) sz.
Proof.
  intros.
  simpl.
  if_tac; [congruence |].
  auto.
Qed.

Lemma sizeof_struct_0: forall env i m,
  sizeof_struct env 0 m = 0 ->
  in_members i m ->
  sizeof env (field_type2 i m) = 0 /\
  field_offset_next env i m 0 - (field_offset2 env i m + sizeof env (field_type2 i m)) = 0.
Proof.
  intros.
  unfold field_type2, field_offset2, field_offset, field_offset_next.
  induction m as [| (i0, t0) m].
  + inversion H0.
  + simpl in H.
    pose proof sizeof_struct_incr env m (align 0 (alignof env t0) + sizeof env t0).
    pose proof align_le 0 (alignof env t0) (alignof_pos _ _).
    pose proof sizeof_pos env t0.
    destruct (ident_eq i i0).
    - simpl in *.
      if_tac; [| congruence].
      replace (sizeof env t0) with 0 by omega.
      destruct m as [| (?, ?) m];
      rewrite !align_0 by apply alignof_pos;
      omega.
    - destruct H0; [simpl in H0; congruence |].
      simpl.
      if_tac; [congruence |].
      replace (sizeof env t0) with 0 by omega.
      destruct m as [| (?, ?) m]; [inversion H0 |].
      rewrite !align_0 by apply alignof_pos.
      apply IHm; [| auto].
      replace (align 0 (alignof env t0) + sizeof env t0) with 0 in * by omega.
      auto.
Qed.

Lemma sizeof_union_0: forall env i m,
  sizeof_union env m = 0 ->
  in_members i m ->
  sizeof env (field_type2 i m) = 0.
Proof.
  intros.
  unfold field_type2.
  induction m as [| (i0, t0) m].
  + inversion H0.
  + simpl in H.
    destruct (ident_eq i i0).
    - simpl in *.
      if_tac; [| congruence].
      pose proof sizeof_pos env t0.
      pose proof Z.le_max_l (sizeof env t0) (sizeof_union env m).
      omega.
    - destruct H0; [simpl in H0; congruence |].
      simpl.
      if_tac; [congruence |].
      apply IHm; [| auto].
      pose proof sizeof_union_pos env m.
      pose proof Z.le_max_r (sizeof env t0) (sizeof_union env m).
      omega.
Qed.

Lemma In_field_type2: forall it m,
  members_no_replicate m = true ->
  In it m ->
  field_type2 (fst it) m = snd it.
Proof.
  unfold field_type2.
  intros.
  induction m.
  + inversion H0.
  + destruct a, it.
    simpl.
    if_tac.
    - destruct H0; [inversion H0; auto |].
      apply in_map with (f := fst) in H0.
      simpl in H0.
      pose proof in_members_tail_no_replicate _ _ _ _ H H0.
      congruence.
    - apply IHm.
      * rewrite members_no_replicate_ind in H.
        tauto.
      * inversion H0; [| auto].
        inversion H2; congruence.
Defined.

End COMPOSITE_ENV.

Module fieldlist.

Definition compute_in_members := @compute_in_members.
Definition field_type := @field_type2.
Definition field_offset := @field_offset2.
Definition field_offset_next := @field_offset_next.

Definition compute_in_members_true_iff: forall i m, compute_in_members i m = true <-> in_members i m
  := @compute_in_members_true_iff.

Definition compute_in_members_false_iff: forall i m,
  compute_in_members i m = false <-> ~ in_members i m
:= @compute_in_members_false_iff.

Ltac destruct_in_members i m :=
  let H := fresh "H" in
  destruct (compute_in_members i m) eqn:H;
    [apply compute_in_members_true_iff in H |
     apply compute_in_members_false_iff in H].

Definition map_members_ext: forall A (f f':ident * type -> A) (m: members),
  members_no_replicate m = true ->
  (forall i, in_members i m -> f (i, field_type i m) = f' (i, field_type i m)) ->
  map f m = map f' m
:= map_members_ext.

Definition field_offset_in_range:
  forall {cs: compspecs},
  forall i m,
  in_members i m ->
  0 <= field_offset cenv_cs i m /\ field_offset cenv_cs i m + sizeof cenv_cs (field_type i m) <= sizeof_struct cenv_cs 0 m
:= @field_offset2_in_range.

Definition sizeof_union_in_members:
  forall {cs: compspecs},
  forall i m,
  in_members i m ->
  sizeof cenv_cs (field_type i m) <= sizeof_union cenv_cs m
:= @sizeof_union_in_members.
(* field_offset_in_range union's version *)

Definition field_offset_no_overlap:
  forall {cs: compspecs},
  forall i1 i2 m,
  i1 <> i2 ->
  in_members i1 m ->
  in_members i2 m ->
  field_offset cenv_cs i1 m + sizeof cenv_cs (field_type i1 m) <= field_offset cenv_cs i2 m \/
  field_offset cenv_cs i2 m + sizeof cenv_cs (field_type i2 m) <= field_offset cenv_cs i1 m
:= @field_offset2_no_overlap.
  
Definition complete_type_field_type:
  forall {cs: compspecs},
  forall id i,
  in_members i (co_members (get_co id)) ->
  complete_type cenv_cs (field_type2 i (co_members (get_co id))) = true
:= @complete_type_field_type2.

Definition field_offset_aligned:
  forall {cs: compspecs},
  forall i m,
  (alignof cenv_cs (field_type i m) | field_offset cenv_cs i m)
:= @field_offset2_aligned.

Definition alignof_field_type_divide_alignof:
  forall {cs: compspecs},
  forall i m,
  in_members i m ->
  (alignof cenv_cs (field_type i m) | alignof_composite cenv_cs m)
:= @alignof_field_type2_divide_alignof.

Definition in_members_field_type:
  forall i m,
  in_members i m ->
  In (i, field_type i m) m
:= @in_members_field_type2.

Definition not_in_members_field_type:
  forall i m,
  ~ in_members i m ->
  field_type i m = Tvoid
:= @not_in_members_field_type2.

Definition not_in_members_field_offset:
  forall {cs: compspecs},
  forall i m,
  ~ in_members i m ->
  field_offset2 cenv_cs i m = 0
:= @not_in_members_field_offset2.

Definition field_offset_next_in_range:
  forall {cs: compspecs},
  forall i m sz,
  in_members i m ->
  sizeof_struct cenv_cs 0 m <= sz ->
  field_offset cenv_cs i m + sizeof cenv_cs (field_type i m) <=
  field_offset_next cenv_cs i m sz <= sz
:= @field_offset_next_in_range.

Definition sizeof_struct_0: forall env i m,
  sizeof_struct env 0 m = 0 ->
  in_members i m ->
  sizeof env (field_type i m) = 0 /\
  field_offset_next env i m 0 - (field_offset env i m + sizeof env (field_type i m)) = 0
:= @sizeof_struct_0.

Definition sizeof_union_0: forall env i m,
  sizeof_union env m = 0 ->
  in_members i m ->
  sizeof env (field_type i m) = 0
:= @sizeof_union_0.

Definition In_field_type: forall it m,
  members_no_replicate m = true ->
  In it m ->
  field_type (fst it) m = snd it
:= @In_field_type2.

End fieldlist.

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