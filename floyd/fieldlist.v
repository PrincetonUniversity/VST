Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Import compcert.lib.Maps.

Arguments align !n !amount / .
Arguments Z.max !n !m / .

Fixpoint plain_members (m: members) : option (list (ident*type)) :=
 match m with
 | Member_plain i t :: m' => match plain_members m' with
                                             | Some l => Some ((i,t)::l)
                                             | None => None
                                             end
 | _ :: _ => None
 | nil => Some nil
 end.

Fixpoint field_type' i (m: list (ident*type)) : option type :=
 match m with
 | (j,t)::m' => if ident_eq i j then Some t else field_type' i m'
 | nil => None
 end.

Fixpoint field_type i (m: list (ident*type)) : type :=
 match m with
 | (j,t)::m' => if ident_eq i j then t else field_type i m'
 | nil => Tvoid
 end.

Lemma field_type_field_type': forall i m,
  field_type i m = match field_type' i m with Some t => t | None => Tvoid end.
Proof.
induction m as [| [? ? ]]; simpl; intros; auto. if_tac; auto.
Qed.

Fixpoint field_offset_rec (env: composite_env) (id: ident) (fld: list (ident*type)) (pos: Z)
                          {struct fld} : Z :=
  match fld with
  | nil => -1
  | (id', t) :: fld' =>
      if ident_eq id id'
      then align pos (@Ctypes.alignof env t)
      else field_offset_rec env id fld' (align pos (@Ctypes.alignof env t) + @Ctypes.sizeof env t)
  end.

Definition field_offset env (i: ident) (m: list (ident*type)) : Z   := field_offset_rec env i m 0.

Fixpoint field_offset_next_rec (env:composite_env) i m ofs sz :=
  match m with
  | nil => 0
  | (i0, t0) :: m0 =>
    match m0 with
    | nil => sz
    | (_, t1) :: _ =>
      if ident_eq i i0
      then align (ofs + @Ctypes.sizeof env t0) (@Ctypes.alignof env t1)
      else field_offset_next_rec env i m0 (align (ofs + @Ctypes.sizeof env t0) (@Ctypes.alignof env t1)) sz
    end
  end.

Definition field_offset_next (env:composite_env) i m sz := field_offset_next_rec env i m 0 sz.

Definition in_members i (m: list (ident*type)): Prop :=
  In i (map fst m).

Definition members_no_replicate (m: list (ident*type)) : bool :=
  compute_list_norepet (map fst m).

Definition compute_in_members id (m: list (ident*type)): bool :=
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

Lemma field_offset_field_type_match': forall cenv i m,
  match field_offset cenv i m, field_type' i m with
  | Zneg _, None => True
  | Zneg _, Some _ => False 
  | _, Some _ => True
  | _, None => False
  end.
Proof.
  intros.
  unfold field_offset.
  set (pos:=0). assert (0 <= pos) by lia. clearbody pos.
  revert pos H; induction m as [| [? ?] ?]; intros.
  + simpl. auto.
  + simpl.
        pose proof (align_le pos _ (Ctypes.alignof_pos t)).
        if_tac. subst.
    - destruct (align pos (Ctypes.alignof t)); auto; lia.
    - apply IHm. pose proof (Ctypes.sizeof_pos t). lia.
Qed.

Lemma field_offset_field_type_match: forall cenv i m,
  match zlt (field_offset cenv i m) 0, field_type' i m with
  | left _, None => True
  | left _, Some _ => False 
  | right _, Some _ => True
  | right _, None => False
  end.
Proof.
  intros.
  pose proof (field_offset_field_type_match' cenv i m).
  destruct (field_offset cenv i m); auto.
Qed.

Lemma field_type_in_members: forall i m,
  match field_type' i m with
  | None => ~ in_members i m
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
    - destruct (field_type' i m).
      * right; auto.
      * intro HH; destruct HH; [congruence | tauto].
Qed.

Section COMPOSITE_ENV.
Context {cs: compspecs}.

Lemma complete_legal_cosu_member: forall (cenv : composite_env) (id : ident) (t : type) (m : members),
  In (Member_plain id t) m -> @composite_complete_legal_cosu_type cenv m = true -> @complete_legal_cosu_type cenv t = true.
Proof.
  intros.
  induction m.
  + inv H.
  + destruct H. subst.
    - 
      simpl in H0.
      rewrite andb_true_iff in H0; tauto.
    - apply IHm; auto.
      simpl in H0.
      rewrite andb_true_iff in H0; tauto.
Qed.         

Lemma in_plain_members:
  forall m m'
  (PLAIN: plain_members m = Some m'),
   forall i t,
  In (Member_plain i t) m <-> In (i,t) m'.
Proof.
 induction m; destruct m'; simpl; intros; try discriminate.
 tauto.
 destruct a.
 destruct (plain_members m); discriminate.
 discriminate.
 destruct a.
 destruct (plain_members m). inv PLAIN.
 specialize (IHm m' (eq_refl _)).
 rewrite <- IHm.
 split; intros [?|?]; auto. inv H; auto. inv H; auto. inv PLAIN. inv PLAIN.
Qed.

Lemma complete_legal_cosu_type_field_type: forall m id
  (PLAIN: plain_members (co_members (get_co id)) = Some m)
  i,
  in_members i m ->
  complete_legal_cosu_type (field_type i m) = true.
Proof.
  unfold get_co.
  intros.
  destruct (cenv_cs ! id) as [co |] eqn:CO.
  + apply in_members_field_type in H.
    pose proof cenv_legal_su _ _ CO.
    apply complete_legal_cosu_member with i (co_members co); eauto.
    apply <- in_plain_members; eauto.
  + simpl in PLAIN. inv PLAIN. inversion H.
Qed.

Lemma plain_members_field_type:
  forall m m' 
  (PLAIN: plain_members m = Some m')
  i, in_members i m' -> Ctypes.field_type i m = Errors.OK (field_type i m').
Proof.
 induction m as [|[|]]; destruct m'; simpl; intros; inv PLAIN. 
 inv H. inv H.
 destruct (plain_members m) eqn:?H; inv H1.
 if_tac. auto.
 inv H. simpl in H1; congruence. apply IHm; auto.
Qed.

Lemma align_bitalign: (* copied from veric/align_mem.v *)
  forall z a, a > 0 ->
    align z a = align (z * 8) (a * 8) / 8.
Proof.
clear.
intros.  unfold align.
rewrite Z.mul_assoc.
rewrite Z.div_mul by congruence.
f_equal.
transitivity ((z + a - 1)*8 / (a*8)).
rewrite Z.div_mul_cancel_r by lia; auto.
rewrite! Z.add_sub_swap.
rewrite Z.mul_add_distr_r.
assert (H0: ((z - 1) * 8 + 1*(a * 8)) / (a * 8) = (z * 8 - 1 + 1*(a * 8)) / (a * 8))
 ; [ | rewrite Z.mul_1_l in H0; auto].
rewrite !Z.div_add by lia.
f_equal.
rewrite Z.mul_sub_distr_r.
rewrite Z.mul_1_l.
rewrite (Z.mul_comm a).
rewrite <- !Zdiv.Zdiv_Zdiv by lia.
f_equal.
transitivity (((z-1)*8)/8).
f_equal; lia.
rewrite Z.div_mul by lia.
rewrite <- !(Z.add_opp_r (_ * _)).
rewrite Z.div_add_l by lia.
reflexivity.
Qed.

Lemma plain_members_field_offset:
  forall m m' 
  (PLAIN: plain_members m = Some m')
  env i, in_members i m' -> Ctypes.field_offset env i m = Errors.OK (field_offset env i m', Full).
Proof.
 unfold field_offset, Ctypes.field_offset.
 intros.
 change 0 with (0*8) at 1.
 generalize 0. revert m' PLAIN H.
 induction m as [|[|]]; destruct m'; simpl; intros; inv PLAIN. 
 inv H. inv H.
 destruct (plain_members m) eqn:?H; inv H1.
 if_tac.
 f_equal. f_equal.
 unfold bitalignof.
 symmetry.
 apply align_bitalign.
 apply Ctypes.alignof_pos.
 inv H. simpl in H1; congruence. 
 rewrite <- (IHm _ (eq_refl _) H2); clear IHm.
 f_equal. unfold bitalignof, bitsizeof.
 symmetry.
 clear.
 pose proof (Ctypes.alignof_pos t).
 pose proof (Ctypes.sizeof_pos t).
 rewrite align_bitalign by auto.
 forget (Ctypes.alignof t) as a.
 forget (Ctypes.sizeof t) as s.
 unfold align.
 replace (z*8+a*8-1) with (z*8-1+1*(a*8)) by lia.
 rewrite !Z.div_add by lia.
 forget (z*8-1) as u.
 rewrite Z.mul_add_distr_r.
 f_equal. rewrite Z.mul_assoc.
 rewrite Z_div_mult by computable.
 f_equal.
Qed.

Lemma align_compatible_rec_Tstruct_inv': forall m id
  (PLAIN: plain_members (co_members (get_co id)) = Some m)
  a ofs,
  align_compatible_rec cenv_cs (Tstruct id a) ofs ->
  forall i,
  in_members i m ->
  align_compatible_rec cenv_cs (field_type i m)
    (ofs + field_offset cenv_cs i m).
Proof.
  unfold get_co.
  intros.
  destruct (cenv_cs ! id) as [co |] eqn:CO.
  + inv H. inv H1.
      inversion2 CO H3.
      apply (H5 i (field_type i m) (field_offset cenv_cs i m)); clear H5.
      apply plain_members_field_type; auto.
      apply plain_members_field_offset; auto.
  + inv PLAIN. inv H0.
Qed.

Lemma align_compatible_rec_Tunion_inv': forall m id
  (PLAIN: plain_members (co_members (get_co id)) = Some m)
  a ofs,
  align_compatible_rec cenv_cs (Tunion id a) ofs ->
  forall i,
  in_members i m ->
  align_compatible_rec cenv_cs (field_type i m) ofs.
Proof.
  unfold get_co.
  intros.
  destruct (cenv_cs ! id) as [co |] eqn:CO.
  + inv H. inv H1.
      inversion2 CO H3.
      apply (H5 i (field_type i m)); clear H5.
      apply plain_members_field_type; auto.
  + inv PLAIN. inv H0.
Qed.

Lemma field_offset_aligned: forall i m,
  (alignof (field_type i m) | field_offset cenv_cs i m).
Proof.
 intros.
 unfold field_offset.
 generalize 0 as pos.
 induction m as [| [? ?]]; simpl; intros.
 apply Z.divide_1_l.
 if_tac.
 apply align_divides. apply alignof_pos.
 apply IHm.
Qed.

Fixpoint alignof_composite (env: composite_env) (m: list (ident*type)) : Z :=
  match m with
  | nil => 1
  | (id, t) :: m' => Z.max (@Ctypes.alignof env t) (alignof_composite env m')
  end.

Lemma alignof_composite_two_p:
  forall env m, exists n, alignof_composite env m = two_power_nat n.
Proof.
  induction m as [|[id t]]; simpl.
- exists 0%nat; auto.
- apply Z.max_case; auto. apply alignof_two_p.
Qed.

Lemma alignof_composite_pos:
  forall env m a, align_attr a (alignof_composite env m) > 0.
Proof.
  intros.
  exploit align_attr_two_p. apply (alignof_composite_two_p env m).
  instantiate (1 := a). intros [n EQ].
  rewrite EQ; apply two_power_nat_pos.
Qed.

Lemma alignof_composite_hd_divide: forall i t m, (alignof t | alignof_composite cenv_cs ((i, t) :: m)).
Proof.
  intros.
  destruct (alignof_two_p t) as [N ?].
  destruct (alignof_composite_two_p cenv_cs ((i, t) :: m)) as [M ?].
  assert (alignof t <= alignof_composite cenv_cs ((i,t)::m)) by (apply Z.le_max_l).
  fold (alignof t) in H.
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

Fixpoint sizeof_struct (env: composite_env) (cur: Z) (m: list(ident*type)) : Z :=
  match m with
  | nil => cur
  | (id, t) :: m' => sizeof_struct env (align cur (@Ctypes.alignof env t) + @Ctypes.sizeof env t) m'
  end.

Fixpoint sizeof_union (env: composite_env) (m: list(ident*type)) : Z :=
  match m with
  | nil => 0
  | (id, t) :: m' => Z.max (@Ctypes.sizeof env t) (sizeof_union env m')
  end.

Ltac solve_field_offset_type i m :=
  let H := fresh "H" in
  let Hty := fresh "H" in
  let Hofs := fresh "H" in
  let t := fresh "t" in
  let ofs := fresh "ofs" in
  pose proof field_offset_field_type_match cenv_cs i m;
  destruct (Ctypes.field_offset cenv_cs i m) as [ofs|?] eqn:Hofs, (Ctypes.field_type i m) as [t|?] eqn:Hty;
    [clear H | inversion H | inversion H | clear H].

Lemma sizeof_struct_incr:
  forall env m cur, cur <= sizeof_struct env cur m.
Proof.
  induction m as [|[id t]]; simpl; intros.
- lia.
- apply Z.le_trans with (align cur (@Ctypes.alignof env t)).
  apply align_le. apply Ctypes.alignof_pos.
  apply Z.le_trans with (align cur (@Ctypes.alignof env t) + @Ctypes.sizeof env t).
  generalize (@Ctypes.sizeof_pos env t); lia.
  apply IHm.
Qed.


Lemma field_offset_rec_in_range:
  forall env id ofs ty fld pos,
  0 <= ofs ->
  field_offset_rec env id fld pos = ofs -> field_type id fld = ty ->
  pos <= ofs /\ ofs + @Ctypes.sizeof env ty <= sizeof_struct env pos fld.
Proof.
  intros until ty. induction fld as [|[i t]]; simpl; intros.
- lia.
- destruct (ident_eq id i).
   subst. split.
  apply align_le. apply Ctypes.alignof_pos. apply sizeof_struct_incr.
  exploit IHfld; eauto. intros [A B]. split; auto.
  eapply Z.le_trans; try apply A. apply Z.le_trans with (align pos (@Ctypes.alignof env t)).
  apply align_le. apply Ctypes.alignof_pos. generalize (@Ctypes.sizeof_pos env t). lia.
Qed.

Lemma in_members_field_offset_pos:
  forall env i m,
  in_members i m -> 0 <= field_offset env i m.
Proof.
 intros.
 unfold field_offset.
 set (pos:=0) at 2.
 assert (0 <= pos) by lia.
 clearbody pos.
 revert pos H0; induction m as [|[??]]; simpl; intros. inv H.
 if_tac. subst. eapply Z.le_trans. apply H0.
 apply align_le. apply Ctypes.alignof_pos.
 destruct H. simpl in H; subst; contradiction. apply IHm; auto.
 pose proof (Ctypes.alignof_pos t). pose proof (Ctypes.sizeof_pos t).
 apply Z.le_trans with (align pos (Ctypes.alignof t)); try lia.
 eapply Z.le_trans. apply H0.
 apply align_le; auto.
Qed.

(* if sizeof Tvoid = 0, this lemma can be nicer. *)
Lemma field_offset_in_range: forall i m,
  in_members i m ->
  0 <= field_offset cenv_cs i m /\ field_offset cenv_cs i m + sizeof (field_type i m) <= sizeof_struct cenv_cs 0 m.
Proof.
  intros.
  pose proof (in_members_field_offset_pos cenv_cs i m H).
  split; auto.
  apply (field_offset_rec_in_range cenv_cs i (field_offset_rec cenv_cs i m 0) (field_type i m) m 0); auto.
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
     lia.
Qed.

Lemma field_offset_no_overlap':
  forall env id1 ofs1 ty1 id2 ofs2 ty2 fld,
  0 <= ofs1 -> 0 <= ofs2 ->
  field_offset env id1 fld = ofs1 -> field_type id1 fld = ty1 ->
  field_offset env id2 fld = ofs2 -> field_type id2 fld = ty2 ->
  id1 <> id2 ->
  ofs1 + @Ctypes.sizeof env ty1 <= ofs2 \/ ofs2 + @Ctypes.sizeof env ty2 <= ofs1.
Proof.
  intros until fld. intros G1 G2. unfold field_offset. generalize 0 as pos.
  induction fld as [|[i t]]; simpl; intros.
- lia.
- destruct (ident_eq id1 i); destruct (ident_eq id2 i).
+ congruence.
+ subst. 
  exploit field_offset_rec_in_range. apply G2. reflexivity. reflexivity. tauto.
+ subst.
  exploit field_offset_rec_in_range. apply G1. reflexivity. reflexivity. tauto.
+ eapply IHfld; eauto.
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
  eapply field_offset_no_overlap'; eauto.
  apply in_members_field_offset_pos; auto.
  apply in_members_field_offset_pos; auto.
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
  field_offset cenv_cs i m = -1.
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
  pattern 0 at 2 3; replace 0 with (align 0 (alignof t0)) by (apply align_0, alignof_pos).
  revert i0 t0 H H0; generalize 0; induction m as [| [i1 t1] m]; intros.
  + destruct (ident_eq i i0); [| destruct H; simpl in H; try congruence; tauto].
    subst; simpl.
    if_tac; [| congruence].
    simpl in H0.
   fold (sizeof t0) in *.
    lia.
  + remember ((i1, t1) :: m) as m0. simpl in H0 |- *. subst m0.
    destruct (ident_eq i i0).
    - split.
      * apply align_le, alignof_pos.
      * pose proof sizeof_struct_incr cenv_cs m (align (align z (alignof t0) + sizeof t0)
            (alignof t1) + sizeof t1).
        pose proof sizeof_pos t1.
        unfold expr.sizeof, expr.alignof in *.
        simpl in H0; lia.
    - destruct H as [H | H]; [simpl in H; congruence |].
      specialize (IHm (align z (alignof t0) + sizeof t0) i1 t1 H H0).
        unfold expr.sizeof, expr.alignof in *.
      destruct (field_offset_rec cenv_cs i ((i1, t1) :: m) (align z (Ctypes.alignof t0) + Ctypes.sizeof t0)),
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

Lemma map_members_ext: forall A (f f':ident * type -> A) (m: list (ident*type)),
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
  field_offset_rec env i m (align z (Ctypes.alignof t0) + Ctypes.sizeof t0).
Proof.
  intros.
  simpl.
  if_tac; [congruence |].
  auto.
Qed.

Lemma neq_field_offset_next_rec_cons: forall env i i0 t0 i1 t1 m z sz,
  i <> i0 ->
  field_offset_next_rec env i ((i0, t0) :: (i1, t1) :: m) z sz =
  field_offset_next_rec env i ((i1, t1) :: m) (align (z +  Ctypes.sizeof t0) (Ctypes.alignof t1)) sz.
Proof.
  intros.
  simpl.
  if_tac; [congruence |].
  auto.
Qed.

Lemma sizeof_struct_0: forall env i m,
  sizeof_struct env 0 m = 0 ->
  in_members i m ->
  Ctypes.sizeof (field_type i m) = 0 /\
  field_offset_next env i m 0 - (field_offset env i m + Ctypes.sizeof (field_type i m)) = 0.
Proof.
  intros.
  unfold field_type, field_offset, Ctypes.field_offset, field_offset_next.
  induction m as [| (i0, t0) m].
  + inversion H0.
  + simpl in H.
    pose proof sizeof_struct_incr env m (align 0 (Ctypes.alignof t0) + Ctypes.sizeof t0).
    pose proof align_le 0 (Ctypes.alignof t0) (Ctypes.alignof_pos _).
    pose proof Ctypes.sizeof_pos t0.
    destruct (ident_eq i i0).
    - simpl in *.
      if_tac; [| congruence].
      replace (Ctypes.sizeof t0) with 0 by lia.
      destruct m as [| (?, ?) m];
      rewrite !align_0 by apply Ctypes.alignof_pos;
      lia.
    - destruct H0; [simpl in H0; congruence |].
      simpl.
      if_tac; [congruence |].
      replace (Ctypes.sizeof t0) with 0 by lia.
      destruct m as [| (?, ?) m]; [inversion H0 |].
      rewrite !align_0 by apply Ctypes.alignof_pos.
      apply IHm; [| auto].
      replace (align 0 (Ctypes.alignof t0) + Ctypes.sizeof t0) with 0 in * by lia.
      auto.
Qed.

Lemma sizeof_union_pos:
  forall env m, 0 <= sizeof_union env m.
Proof.
  induction m as [|[id t]]; simpl; extlia.
Qed.

Lemma sizeof_union_0: forall env i m,
  sizeof_union env m = 0 ->
  in_members i m ->
  Ctypes.sizeof (field_type i m) = 0.
Proof.
  intros.
  induction m as [| (i0, t0) m].
  + inversion H0.
  + simpl in H.
    destruct (ident_eq i i0).
    - simpl in *.
      if_tac; [| congruence].
      pose proof Ctypes.sizeof_pos t0.
      pose proof Z.le_max_l (Ctypes.sizeof t0) (sizeof_union env m).
      lia.
    - destruct H0; [simpl in H0; congruence |].
      simpl.
      if_tac; [congruence |].
      apply IHm; [| auto].
      pose proof sizeof_union_pos env m.
      pose proof Z.le_max_r (Ctypes.sizeof t0) (sizeof_union env m).
      lia.
Qed.

Definition in_map: forall {A B : Type} (f : A -> B) (l : list A) (x : A),
       In x l -> In (f x) (map f l) :=
fun {A B : Type} (f : A -> B) (l : list A) =>
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

Lemma members_spec_change_composite' {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: 
  forall id m
  (PLAIN: plain_members (co_members (@get_co cs_to id)) = Some m),
  match (coeq cs_from cs_to) ! id with
  | Some b => test_aux cs_from cs_to b id
  | None => false
  end = true ->
  Forall (fun it => cs_preserve_type cs_from cs_to (coeq _ _) (snd it) = true) m.
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
    unfold get_co in PLAIN.
    rewrite H0 in PLAIN.
    clear - H1 PLAIN.
    symmetry in H1.
    revert m PLAIN; induction (co_members c) as [|[|]]; intros.
    - inv PLAIN. constructor.
    - simpl in PLAIN. destruct (plain_members m) eqn:?H; inv PLAIN.
       simpl in H1; rewrite andb_true_iff in H1; destruct H1.
      constructor; auto.
    - inv PLAIN.
  + destruct ((coeq cs_from cs_to) ! id) eqn:?H.
    - pose proof proj2 (coeq_complete _ _ id) (ex_intro _ b H1) as [co ?].
      congruence.
    - inv H.
Qed.

Lemma members_spec_change_composite'delete_me {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall id,
  match (coeq cs_from cs_to) ! id with
  | Some b => test_aux cs_from cs_to b id
  | None => false
  end = true ->
  Forall (fun m => cs_preserve_type cs_from cs_to (coeq _ _) (type_member m) = true) (co_members (@get_co cs_to id)).
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
    induction (co_members c).
    - constructor.
    - simpl in H1; rewrite andb_true_iff in H1; destruct H1.
      constructor; auto.
  + destruct ((coeq cs_from cs_to) ! id) eqn:?H.
    - pose proof proj2 (coeq_complete _ _ id) (ex_intro _ b H1) as [co ?].
      congruence.
    - inv H.
Qed.

Lemma members_spec_change_composite'' {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}:
  forall id m
  (PLAIN: plain_members (co_members (@get_co cs_to id)) = Some m),
  match (coeq cs_from cs_to) ! id with
  | Some b => test_aux cs_from cs_to b id
  | None => false
  end = true ->
  forall i, cs_preserve_type cs_from cs_to (coeq _ _) (field_type i m) = true.
Proof.
  intros.
  apply (@members_spec_change_composite' cs_from cs_to _ _ _ PLAIN) in H.
  clear PLAIN.
  induction H as [|[??]]; auto.
  simpl; if_tac; auto.
Qed.

Definition field_type'' i m := match Ctypes.field_type i m with Errors.OK t => t | _ => Tvoid end.
Lemma members_spec_change_composite''_delete_me {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall id,
  match (coeq cs_from cs_to) ! id with
  | Some b => test_aux cs_from cs_to b id
  | None => false
  end = true ->
  forall i, cs_preserve_type cs_from cs_to (coeq _ _) (field_type'' i (co_members (get_co id))) = true.
Proof.
  intros.
  unfold field_type''.
  apply members_spec_change_composite'delete_me in H.
  induction H as [|[|]]; auto;
  simpl; if_tac; auto.
Qed.

Lemma plain_members_no_replicate:
  forall {cs: compspecs} (id: positive) m, 
    plain_members (co_members (get_co id)) = Some m ->
    members_no_replicate m = true.
Proof.
 intros.
 pose proof (get_co_members_no_replicate id).
 unfold members_no_replicate.
 unfold mpred.members_no_replicate in H0.
 revert m H; induction (co_members (get_co id)) as [|[|]]; intros.
 -
 inv H. reflexivity.
 -
 simpl in *.
 destruct (plain_members m) eqn:?H; inv H.
 simpl.
 destruct (id_in_list id0 (map fst l)) eqn:?H;
 destruct (id_in_list id0 (map name_member m)) eqn:?H; auto.
 clear - H2 H1 H.
 revert l H1 H; induction m as [|[|]]; simpl; intros. inv H1. inv H.
 destruct (plain_members m) eqn:?H; inv H1.
 simpl map in H2,H.
 unfold id_in_list in H2,H; fold id_in_list in H2,H.
 rewrite orb_false_iff in H2.
 rewrite orb_true_iff in H. destruct H2,H; try tauto; try congruence; eauto.
 inv H1.
 inv H0.
 -
  inv H.
Qed.
 
Lemma members_spec_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}:
  forall id m
  (PLAIN: plain_members (co_members (@get_co cs_to id)) = Some m),
  match (coeq cs_from cs_to) ! id with
  | Some b => test_aux cs_from cs_to b id
  | None => false
  end = true ->
  Forall (fun it => cs_preserve_type cs_from cs_to (coeq _ _) (field_type (fst it) m) = true) m.
Proof.
  intros.
  apply (members_spec_change_composite' _ _ PLAIN) in H.
  assert (Forall (fun it: ident * type => field_type (fst it) m = snd it) m).
  1:{
    rewrite Forall_forall.
    intros it ?.
    apply In_field_type; auto.
    apply plain_members_no_replicate in PLAIN; auto.
  }
  revert H0.
 clear PLAIN.
 generalize m at 1 3.
  induction H as [| [i t] ?]; constructor.
  + inv H1.
    simpl in *.
    rewrite H4; auto.
  + inv H1. 
    auto.
Qed.

Lemma members_spec_change_composite_delete_me {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall id,
  match (coeq cs_from cs_to) ! id with
  | Some b => test_aux cs_from cs_to b id
  | None => false
  end = true ->
  Forall (fun m => cs_preserve_type cs_from cs_to (coeq _ _) (field_type'' (name_member m) (co_members (get_co id))) = true) (co_members (get_co id)).
Proof.
  intros.
  apply members_spec_change_composite'delete_me in H.
  assert (Forall (fun m: member => field_type'' (name_member m) (co_members (get_co id)) = type_member m) (co_members (get_co id))).
  1:{
    rewrite Forall_forall.
    intros it ?.
    clear - H0.
    pose proof (get_co_members_no_replicate id).
    apply compute_list_norepet_e in H.
    induction (co_members (get_co id)) as [|[|]]. inv H0. inv H.
    -
    unfold field_type''; simpl.
    destruct H0. subst. 
    if_tac. auto. simpl in H. contradiction.
    if_tac. subst id0. contradiction H3. clear - H.
    apply (in_map name_member) in H. auto.
    apply IHm; auto. 
    -
    unfold field_type''; simpl.
    destruct H0. subst. 
    if_tac. auto. simpl in H. contradiction.
    inv H.
    if_tac. subst id0. contradiction H3. clear - H0.
    apply (in_map name_member) in H0. auto.
    apply IHm; auto. 
  }
  revert H0; generalize (co_members (get_co id)) at 1 3.
  induction H; constructor.
  + inv H1.
    simpl in *.
    rewrite H4; auto.
  + inv H1.
    auto.
Qed.

(* TODO: we have already proved a related field_offset lemma in veric/change_compspecs.v. But it seems not clear how to use that in an elegant way. *)
Lemma field_offset_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: 
  forall id m
  (PLAIN: plain_members (co_members (@get_co cs_to id)) = Some m)
  i,
  match (coeq cs_from cs_to) ! id with
  | Some b => test_aux cs_from cs_to b id
  | None => false
  end = true ->
  field_offset (@cenv_cs cs_from) i m =
  field_offset (@cenv_cs cs_to) i m.
Proof.
  intros.
  apply (members_spec_change_composite' _ _ PLAIN) in H. clear PLAIN.
  unfold field_offset.
  generalize 0.
  induction m as [| [i0 t0] ?]; intros.
  + auto.
  + simpl.
    inv H.
    if_tac.
    - f_equal.
      apply alignof_change_composite; auto.
    - specialize (IHm H3).
       fold (@alignof cs_from t0) in *. fold (@sizeof cs_from t0) in *.
       fold (@alignof cs_to t0) in *. fold (@sizeof cs_to t0) in *.
      rewrite alignof_change_composite, sizeof_change_composite by auto.
      apply IHm.
Qed.

Lemma field_offset_next_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: 
  forall id m
  (PLAIN: plain_members (co_members (@get_co cs_to id)) = Some m)
  i,
  match (coeq cs_from cs_to) ! id with
  | Some b => test_aux cs_from cs_to b id
  | None => false
  end = true ->
  field_offset_next (@cenv_cs cs_from) i m (co_sizeof (@get_co cs_from id)) =
  field_offset_next (@cenv_cs cs_to) i m (co_sizeof (@get_co cs_to id)).
Proof.
  intros.
  rewrite co_sizeof_get_co_change_composite by auto.
  apply (members_spec_change_composite' _ _ PLAIN) in H. clear PLAIN.
  unfold field_offset_next.
  generalize 0.
  destruct H as [| [i0 t0] ? ]; intros; auto.
  simpl in H, H0.
  revert i0 t0 H z.
  induction H0 as [| [i1 t1] ? ]; intros.
  + reflexivity.
  + simpl.
       fold (@alignof cs_from t0) in *. fold (@sizeof cs_from t0) in *.
       fold (@alignof cs_to t0) in *. fold (@sizeof cs_to t0) in *.
       fold (@alignof cs_from t1) in *. fold (@sizeof cs_from t1) in *.
       fold (@alignof cs_to t1) in *. fold (@sizeof cs_to t1) in *.
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

