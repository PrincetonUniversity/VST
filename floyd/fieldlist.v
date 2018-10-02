Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.

Arguments align !n !amount / .
Arguments Z.max !n !m / .

Definition field_type i m :=
  match Ctypes.field_type i m with
  | Errors.OK t => t
  | _ => Tvoid
  end.

Definition field_offset env i m :=
  match Ctypes.field_offset env i m with
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
      then align (ofs + @sizeof env t0) (@alignof env t1)
      else field_offset_next_rec env i m0 (align (ofs + @sizeof env t0) (@alignof env t1)) sz
    end
  end.

Definition field_offset_next env i m sz := field_offset_next_rec env i m 0 sz.

Lemma in_members_field_type: forall i m,
  in_members i m ->
  In (i, field_type i m) m.
Proof.
  intros.
  unfold field_type.
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
  match Ctypes.field_offset cenv i m, Ctypes.field_type i m with
  | Errors.OK _, Errors.OK _ => True
  | Errors.Error _, Errors.Error _ => True
  | _, _ => False
  end.
Proof.
  intros.
  unfold Ctypes.field_offset.
  remember 0 as pos; clear Heqpos.
  revert pos; induction m as [| [? ?] ?]; intros.
  + simpl. auto.
  + simpl. destruct (ident_eq i i0) eqn:HH.
    - auto.
    - apply IHm.
Defined.

Lemma field_type_in_members: forall i m,
  match Ctypes.field_type i m with
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
    - destruct (Ctypes.field_type i m).
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
  destruct (Ctypes.field_offset cenv_cs i m) as [ofs|?] eqn:Hofs, (Ctypes.field_type i m) as [t|?] eqn:Hty;
    [clear H | inversion H | inversion H | clear H].

Lemma complete_legal_cosu_member: forall (cenv : composite_env) (id : ident) (t : type) (m : list (ident * type)),
  In (id, t) m -> @composite_complete_legal_cosu_type cenv m = true -> @complete_legal_cosu_type cenv t = true.
Proof.
  intros.
  induction m as [| [i0 t0] ?].
  + inv H.
  + destruct H.
    - inv H.
      simpl in H0.
      rewrite andb_true_iff in H0; tauto.
    - apply IHm; auto.
      simpl in H0.
      rewrite andb_true_iff in H0; tauto.
Qed.         

Lemma complete_legal_cosu_type_field_type: forall id i,
  in_members i (co_members (get_co id)) ->
  complete_legal_cosu_type (field_type i (co_members (get_co id))) = true.
Proof.
  unfold get_co.
  intros.
  destruct (cenv_cs ! id) as [co |] eqn:CO.
  + apply in_members_field_type in H.
    pose proof cenv_legal_su _ _ CO.
    eapply complete_legal_cosu_member; eauto.
  + inversion H.
Qed.

Lemma align_compatible_rec_Tstruct_inv': forall id a ofs,
  align_compatible_rec cenv_cs (Tstruct id a) ofs ->
  forall i,
  in_members i (co_members (get_co id)) ->
  align_compatible_rec cenv_cs (field_type i (co_members (get_co id)))
    (ofs + field_offset cenv_cs i (co_members (get_co id))).
Proof.
  unfold get_co.
  intros.
  destruct (cenv_cs ! id) as [co |] eqn:CO.
  + eapply align_compatible_rec_Tstruct_inv with (i0 := i); try eassumption.
    - unfold field_type.
      induction (co_members co) as [| [i0 t0] ?].
      * inv H0.
      * simpl; if_tac; auto.
        apply IHm.
        destruct H0; [simpl in H0; congruence | auto].
    - unfold field_offset, Ctypes.field_offset.
      generalize 0 at 1 2.
      induction (co_members co) as [| [i0 t0] ?]; intros.
      * inv H0.
      * simpl; if_tac; auto.
        apply IHm.
        destruct H0; [simpl in H0; congruence | auto].
  + inv H0.
Qed.

Lemma align_compatible_rec_Tunion_inv': forall id a ofs,
  align_compatible_rec cenv_cs (Tunion id a) ofs ->
  forall i,
  in_members i (co_members (get_co id)) ->
  align_compatible_rec cenv_cs (field_type i (co_members (get_co id))) ofs.
Proof.
  unfold get_co.
  intros.
  destruct (cenv_cs ! id) as [co |] eqn:CO.
  + eapply align_compatible_rec_Tunion_inv with (i0 := i); try eassumption.
    unfold field_type.
    induction (co_members co) as [| [i0 t0] ?].
    - inv H0.
    - simpl; if_tac; auto.
      apply IHm.
      destruct H0; [simpl in H0; congruence | auto].
  + inv H0.
Qed.

Lemma field_offset_aligned: forall i m,
  (alignof (field_type i m) | field_offset cenv_cs i m).
Proof.
  intros.
  unfold field_type, field_offset.
  solve_field_offset_type i m.
  + eapply field_offset_aligned; eauto.
  + apply Z.divide_0_r.
Qed.

Lemma alignof_composite_hd_divide: forall i t m, (alignof t | alignof_composite cenv_cs ((i, t) :: m)).
Proof.
  intros.
  destruct (alignof_two_p t) as [N ?].
  destruct (alignof_composite_two_p cenv_cs ((i, t) :: m)) as [M ?].
  assert (alignof t <= alignof_composite cenv_cs ((i,t)::m)) by (apply Z.le_max_l).
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

Lemma alignof_field_type_divide_alignof: forall i m,
  in_members i m ->
  (alignof (field_type i m) | alignof_composite cenv_cs m).
Proof.
  intros.
  unfold field_type.
  induction m as [| [i0 t0] m].
  + inversion H.
  + unfold in_members in H; simpl in H.
    simpl Ctypes.field_type.
    if_tac.
    - apply alignof_composite_hd_divide.
    - eapply Z.divide_trans.
      * apply IHm.
        destruct H; [congruence | auto].
      * apply alignof_composite_tl_divide.
Qed.

(* if sizeof Tvoid = 0, this lemma can be nicer. *)
Lemma field_offset_in_range: forall i m,
  in_members i m ->
  0 <= field_offset cenv_cs i m /\ field_offset cenv_cs i m + sizeof (field_type i m) <= sizeof_struct cenv_cs 0 m.
Proof.
  intros.
  unfold field_offset, field_type.
  solve_field_offset_type i m.
  + eapply field_offset_in_range; eauto.
  + pose proof field_type_in_members i m.
    rewrite H1 in H0.
    tauto.
Qed.

(* if sizeof Tvoid = 0, this lemma can be nicer. *)
Lemma sizeof_union_in_members: forall i m,
  in_members i m ->
  sizeof (field_type i m) <= sizeof_union cenv_cs m.
(* field_offset2_in_range union's version *)
Proof.
  intros.
  unfold in_members in H.
  unfold field_type.
  induction m as [|[i0 t0] m].
  + inversion H.
  + simpl.
    destruct (ident_eq i i0).
    - apply Z.le_max_l.
    - simpl in H; destruct H; [congruence |].
     specialize (IHm H).
     fold (sizeof t0).
     pose proof Z.le_max_r (sizeof t0) (sizeof_union cenv_cs m).
     omega.
Qed.

(* if sizeof Tvoid = 0, this lemma can be nicer. *)
Lemma field_offset_no_overlap:
  forall i1 i2 m,
  i1 <> i2 ->
  in_members i1 m ->
  in_members i2 m ->
  field_offset cenv_cs i1 m + sizeof (field_type i1 m) <= field_offset cenv_cs i2 m \/
  field_offset cenv_cs i2 m + sizeof (field_type i2 m) <= field_offset cenv_cs i1 m.
Proof.
  intros.
  unfold field_offset, field_type.
  pose proof field_type_in_members i1 m.
  pose proof field_type_in_members i2 m.
  solve_field_offset_type i1 m;
  solve_field_offset_type i2 m; try tauto.
  eapply field_offset_no_overlap; eauto.
Qed.

Lemma not_in_members_field_type: forall i m,
  ~ in_members i m ->
  field_type i m = Tvoid.
Proof.
  unfold in_members, field_type.
  intros.
  induction m as [| [i0 t0] m].
  + reflexivity.
  + simpl in H.
    simpl.
    destruct (ident_eq i i0) as [HH | HH]; pose proof (@eq_sym ident i i0); tauto.
Qed.

Lemma not_in_members_field_offset: forall i m,
  ~ in_members i m ->
  field_offset cenv_cs i m = 0.
Proof.
  unfold in_members, field_offset, Ctypes.field_offset.
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
  field_offset cenv_cs i m + sizeof (field_type i m) <=
  field_offset_next cenv_cs i m sz <= sz.
Proof.
  intros.
  destruct m as [| [i0 t0] m]; [inversion H |].
  unfold field_offset, Ctypes.field_offset, field_offset_next, field_type.
  pattern 0 at 3 4; replace 0 with (align 0 (alignof t0)) by (apply align_0, alignof_pos).
  match goal with
  | |- ?A => assert (A /\
                     match field_offset_rec cenv_cs i ((i0, t0) :: m) 0 with
                     | Errors.OK _ => True
                     | _ => False
                     end /\
                     match Ctypes.field_type i ((i0, t0) :: m) with
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
   fold (sizeof t0) in *.
    omega.
  + remember ((i1, t1) :: m) as m0. simpl in H0 |- *. subst m0.
    destruct (ident_eq i i0).
    - split; [| split]; auto.
      split.
      * apply align_le, alignof_pos.
      * pose proof sizeof_struct_incr cenv_cs m (align (align z (alignof t0) + sizeof t0)
            (alignof t1) + sizeof t1).
        pose proof sizeof_pos t1.
        simpl in H0; omega.
    - destruct H as [H | H]; [simpl in H; congruence |].
      specialize (IHm (align z (alignof t0) + sizeof t0) i1 t1 H H0).
      destruct (field_offset_rec cenv_cs i ((i1, t1) :: m) (align z (alignof t0) + sizeof t0)),
               (field_type i ((i1, t1) :: m));
      try tauto.
Qed.

Lemma Pos_eqb_eq: forall p q: positive, iff (eq (Pos.eqb p q) true) (eq p q).
Proof.
intros.
split.
revert q; induction p; destruct q; simpl; intros; auto; try discriminate.
apply f_equal. apply IHp; auto.
apply f_equal. apply IHp; auto.
intros; subst.
induction q; simpl; auto.
Defined.


(* copied from veric/Clight_lemmas.v; but here Defined instead of Qed  *)
Lemma id_in_list_true: forall i ids, id_in_list i ids = true -> In i ids.
Proof.
 induction ids; simpl; intros. inv H.
 destruct (i =? a)%positive eqn:?.
 apply Pos_eqb_eq in Heqb. left; auto.
 auto.
Defined.


Lemma id_in_list_false: forall i ids, id_in_list i ids = false -> ~In i ids.
Proof.
 intros.
 intro. induction ids. inv H0.
 simpl in *. destruct H0. subst i.
 assert (a =? a = true)%positive.
 apply Pos_eqb_eq. auto. rewrite H0 in H. simpl in H. inv H.
 destruct (i =? a)%positive. simpl in H. inv H.   auto.
Defined.

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
       split; intros. inv H.  destruct H. elimtype False; apply H.
      apply HH.
    - apply id_in_list_false in HH.
      split; intros. split; auto. destruct H; auto.
Defined.

Lemma map_members_ext: forall A (f f':ident * type -> A) (m: members),
  members_no_replicate m = true ->
  (forall i, in_members i m -> f (i, field_type i m) = f' (i, field_type i m)) ->
  map f m = map f' m.
Proof.
  intros.
  induction m as [| (i0, t0) m].
  + reflexivity.
  + simpl.
    rewrite members_no_replicate_ind in H.
    f_equal.
    - specialize (H0 i0).
      unfold field_type, in_members in H0.
      simpl in H0; if_tac in H0; [| congruence].
      apply H0; auto.
    - apply IHm; [tauto |].
      intros.
      specialize (H0 i).
      unfold field_type, in_members in H0.
      simpl in H0; if_tac in H0; [subst; tauto |].
      apply H0; auto.
Defined.

Lemma in_members_tail_no_replicate: forall i i0 t0 m,
  members_no_replicate ((i0, t0) :: m) = true ->
  in_members i m ->
  i <> i0.
Proof.
  intros.
 destruct (members_no_replicate_ind ((i0,t0)::m)) as [? _].
 apply H1 in H. clear H1.
  intro.
  subst. destruct H. auto.
Defined.

Lemma neq_field_offset_rec_cons: forall env i i0 t0 m z,
  i <> i0 ->
  field_offset_rec env i ((i0, t0) :: m) z =
  field_offset_rec env i m (align z (alignof t0) + sizeof t0).
Proof.
  intros.
  simpl.
  if_tac; [congruence |].
  auto.
Qed.

Lemma neq_field_offset_next_rec_cons: forall env i i0 t0 i1 t1 m z sz,
  i <> i0 ->
  field_offset_next_rec env i ((i0, t0) :: (i1, t1) :: m) z sz =
  field_offset_next_rec env i ((i1, t1) :: m) (align (z +  sizeof t0) (alignof t1)) sz.
Proof.
  intros.
  simpl.
  if_tac; [congruence |].
  auto.
Qed.

Lemma sizeof_struct_0: forall env i m,
  sizeof_struct env 0 m = 0 ->
  in_members i m ->
  sizeof (field_type i m) = 0 /\
  field_offset_next env i m 0 - (field_offset env i m + sizeof (field_type i m)) = 0.
Proof.
  intros.
  unfold field_type, field_offset, Ctypes.field_offset, field_offset_next.
  induction m as [| (i0, t0) m].
  + inversion H0.
  + simpl in H.
    pose proof sizeof_struct_incr env m (align 0 (alignof t0) + sizeof t0).
    pose proof align_le 0 (alignof t0) (alignof_pos _).
    pose proof sizeof_pos t0.
    destruct (ident_eq i i0).
    - simpl in *.
      if_tac; [| congruence].
      replace (sizeof t0) with 0 by omega.
      destruct m as [| (?, ?) m];
      rewrite !align_0 by apply alignof_pos;
      omega.
    - destruct H0; [simpl in H0; congruence |].
      simpl.
      if_tac; [congruence |].
      replace (sizeof t0) with 0 by omega.
      destruct m as [| (?, ?) m]; [inversion H0 |].
      rewrite !align_0 by apply alignof_pos.
      apply IHm; [| auto].
      replace (align 0 (alignof t0) + sizeof t0) with 0 in * by omega.
      auto.
Qed.

Lemma sizeof_union_0: forall env i m,
  sizeof_union env m = 0 ->
  in_members i m ->
  sizeof (field_type i m) = 0.
Proof.
  intros.
  unfold field_type.
  induction m as [| (i0, t0) m].
  + inversion H0.
  + simpl in H.
    destruct (ident_eq i i0).
    - simpl in *.
      if_tac; [| congruence].
      pose proof sizeof_pos t0.
      pose proof Z.le_max_l (sizeof t0) (sizeof_union env m).
      omega.
    - destruct H0; [simpl in H0; congruence |].
      simpl.
      if_tac; [congruence |].
      apply IHm; [| auto].
      pose proof sizeof_union_pos env m.
      pose proof Z.le_max_r (sizeof t0) (sizeof_union env m).
      omega.
Qed.

Definition in_map: forall {A B : Type} (f : A -> B) (l : list A) (x : A),
       In x l -> In (f x) (map f l) :=
fun (A B : Type) (f : A -> B) (l : list A) =>
list_ind (fun l0 : list A => forall x : A, In x l0 -> In (f x) (map f l0))
  (fun (x : A) (H : In x nil) => H)
  (fun (a : A) (l0 : list A)
     (IHl : forall x : A, In x l0 -> In (f x) (map f l0)) (x : A)
     (H : In x (a :: l0)) =>
   or_ind
     (fun H0 : a = x =>
      or_introl (eq_ind_r (fun a0 : A => f a0 = f x) eq_refl H0))
     (fun H0 : In x l0 =>
      or_intror
        ((fun H1 : In x l0 -> In (f x) (map f l0) =>
          (fun H2 : In (f x) (map f l0) => H2) (H1 H0)) (IHl x))) H) l.

Lemma In_field_type: forall it m,
  members_no_replicate m = true ->
  In it m ->
  field_type (fst it) m = snd it.
Proof.
  unfold field_type.
  intros.
  induction m.
  + inversion H0.
  + destruct a, it.
    simpl.
    destruct (ident_eq i0 i).
    - destruct H0; [inversion H0; auto |].
      apply in_map with (f := fst) in H0.
      simpl in H0.
      pose proof in_members_tail_no_replicate _ _ _ _ H H0.
      subst i0. contradiction H1; auto.
    - apply IHm.
       destruct (members_no_replicate_ind ((i,t)::m)) as [? _].
       destruct (H1 H); auto.
      * inversion H0; [| auto].
        inversion H1. subst i0 t0.  contradiction n; auto.
Defined.

End COMPOSITE_ENV.

Lemma members_spec_change_composite' {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall id,
  match (coeq cs_from cs_to) ! id with
  | Some b => test_aux cs_from cs_to b id
  | None => false
  end = true ->
  Forall (fun it => cs_preserve_type cs_from cs_to (coeq _ _) (snd it) = true) (co_members (get_co id)).
Proof.
  intros.
  destruct ((@cenv_cs cs_to) ! id) eqn:?H.
  + pose proof proj1 (coeq_complete _ _ id) (ex_intro _ c H0) as [b ?].
    rewrite H1 in H.
    apply (coeq_consistent _ _ id _ _ H0) in H1.
    unfold test_aux in H.
    destruct b; [| inv H].
    rewrite !H0 in H.
    destruct ((@cenv_cs cs_from) ! id) eqn:?H; [| inv H].
    simpl in H.
    rewrite !andb_true_iff in H.
    unfold get_co.
    rewrite H0.
    clear - H1.
    symmetry in H1.
    induction (co_members c) as [| [i t] ?].
    - constructor.
    - simpl in H1; rewrite andb_true_iff in H1; destruct H1.
      constructor; auto.
  + destruct ((coeq cs_from cs_to) ! id) eqn:?H.
    - pose proof proj2 (coeq_complete _ _ id) (ex_intro _ b H1) as [co ?].
      congruence.
    - inv H.
Qed.

Lemma members_spec_change_composite'' {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall id,
  match (coeq cs_from cs_to) ! id with
  | Some b => test_aux cs_from cs_to b id
  | None => false
  end = true ->
  forall i, cs_preserve_type cs_from cs_to (coeq _ _) (field_type i (co_members (get_co id))) = true.
Proof.
  intros.
  unfold field_type.
  apply members_spec_change_composite' in H.
  induction H as [| [i0 t0] ?]; auto.
  simpl.
  if_tac; auto.
Qed.

Lemma members_spec_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall id,
  match (coeq cs_from cs_to) ! id with
  | Some b => test_aux cs_from cs_to b id
  | None => false
  end = true ->
  Forall (fun it => cs_preserve_type cs_from cs_to (coeq _ _) (field_type (fst it) (co_members (get_co id))) = true) (co_members (get_co id)).
Proof.
  intros.
  apply members_spec_change_composite' in H.
  assert (Forall (fun it: ident * type => field_type (fst it) (co_members (get_co id)) = snd it) (co_members (get_co id))).
  1:{
    rewrite Forall_forall.
    intros it ?.
    apply In_field_type; auto.
    apply get_co_members_no_replicate.
  }
  revert H0; generalize (co_members (get_co id)) at 1 3.
  induction H as [| [i t] ?]; constructor.
  + inv H1.
    simpl in *.
    rewrite H4; auto.
  + inv H1.
    auto.
Qed.

(* TODO: we have already proved a related field_offset lemma in veric/change_compspecs.v. But it seems not clear how to use that in an elegant way. *)
Lemma field_offset_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall id i,
  match (coeq cs_from cs_to) ! id with
  | Some b => test_aux cs_from cs_to b id
  | None => false
  end = true ->
  field_offset (@cenv_cs cs_from) i (co_members (@get_co cs_to id)) =
  field_offset (@cenv_cs cs_to) i (co_members (@get_co cs_to id)).
Proof.
  intros.
  apply members_spec_change_composite' in H.
  unfold field_offset, Ctypes.field_offset.
  generalize 0 at 1 3.
  induction (co_members (get_co id)) as [| [i0 t0] ?]; intros.
  + auto.
  + simpl.
    inv H.
    if_tac.
    - f_equal.
      apply alignof_change_composite; auto.
    - specialize (IHm H3).
      rewrite alignof_change_composite, sizeof_change_composite by auto.
      apply IHm.
Qed.

Lemma field_offset_next_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall id i,
  match (coeq cs_from cs_to) ! id with
  | Some b => test_aux cs_from cs_to b id
  | None => false
  end = true ->
  field_offset_next (@cenv_cs cs_from) i (co_members (get_co id)) (co_sizeof (@get_co cs_from id)) =
field_offset_next (@cenv_cs cs_to) i (co_members (get_co id)) (co_sizeof (@get_co cs_to id)).
Proof.
  intros.
  rewrite co_sizeof_get_co_change_composite by auto.
  apply members_spec_change_composite' in H.
  unfold field_offset_next.
  generalize 0.
  destruct H as [| [i0 t0] ? ]; intros; auto.
  simpl in H, H0.
  revert i0 t0 H z.
  induction H0 as [| [i1 t1] ? ]; intros.
  + reflexivity.
  + simpl.
    if_tac; auto.
    - f_equal; [f_equal |].
      * apply sizeof_change_composite; auto.
      * apply alignof_change_composite; auto.
    - specialize (IHForall i1 t1 H (align (z + sizeof t0) (alignof t1))); simpl in IHForall.
      rewrite (sizeof_change_composite t0) by auto.
      rewrite (alignof_change_composite t1) by auto.
      apply IHForall.
Qed.

Arguments field_type i m / .
Arguments field_offset env i m / .

