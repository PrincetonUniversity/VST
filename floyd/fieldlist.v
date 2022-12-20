Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Import compcert.lib.Maps.

Arguments align !n !amount / .
Arguments Z.max !n !m / .

Definition field_type i (m: members) : type :=
 match Ctypes.field_type i m with
 | Errors.OK t => t 
 | _ => Tvoid
 end.

Fixpoint field_offset_rec (env: composite_env) (id: ident) (fld: list member) (pos: Z)
                          {struct fld} : Z :=
  match fld with
  | Member_plain id' t :: fld' =>
      if ident_eq id id'
      then align pos (@Ctypes.alignof env t)
      else field_offset_rec env id fld' (align pos (@Ctypes.alignof env t) + @Ctypes.sizeof env t)
  | _ => -1
  end.

Definition field_offset env (i: ident) (m: members) : Z   := field_offset_rec env i m 0.

Fixpoint field_offset_next_rec (env:composite_env) i m ofs sz :=
  match m with
  | Member_plain i0 t0 :: m0 =>
    match m0 with
    | nil => sz
    | m1 :: _ =>
      if ident_eq i i0
      then align (ofs + @Ctypes.sizeof env t0) (@Ctypes.alignof env (type_member m1))
      else field_offset_next_rec env i m0 (align (ofs + @Ctypes.sizeof env t0) (@Ctypes.alignof env (type_member m1))) sz
    end
  | _ => 0
  end.

Definition field_offset_next (env:composite_env) i m sz := field_offset_next_rec env i m 0 sz.

Definition in_members i (m: members): Prop :=
  In i (map name_member m).

Definition compute_in_members id (m: members): bool :=
  id_in_list id (map name_member m).

Lemma compute_in_members_true_iff: forall i m, compute_in_members i m = true <-> in_members i m.
Proof.
  intros.
  unfold compute_in_members.
  destruct (id_in_list i (map name_member m)) eqn:HH;
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

Lemma in_members_field_type': forall i m,
  in_members i m ->
  exists a, name_member a = i /\ type_member a = (field_type i m) /\ In a m.
Proof.
  unfold field_type.
  intros.
  induction m as [|[|] m].
  + inversion H.
  + unfold in_members in H; simpl in *.
    if_tac.
    - subst. eexists. split3; [ | |left; reflexivity]; eauto.
    - destruct H. congruence. destruct (IHm H) as [a [? [??]]].  exists a; split3; auto.
  + unfold in_members in H; simpl in *.
    if_tac.
    - subst. eexists. split3; [ | |left; reflexivity]; eauto.
    - destruct H. congruence. destruct (IHm H) as [b [? [??]]].  exists b; split3; auto.
Qed.

Lemma in_members_field_type: forall i m
  (PLAIN: plain_members m = true),
  in_members i m ->
  In (Member_plain i (field_type i m)) m.
Proof.
  unfold field_type.
  intros.
  induction m as [|[|] m].
  + inversion H.
  + unfold in_members in H; simpl in *.
    if_tac.
    - subst. auto.
    - right. apply IHm; auto. destruct H; auto. congruence. 
  + simpl in PLAIN. congruence.
Qed.

Lemma field_offset_field_type_match: forall cenv i m
  (PLAIN: plain_members m = true),
  match Ctypes.field_offset cenv i m, Ctypes.field_type i m with
  | Errors.OK _, Errors.OK _ => True
  | Errors.Error _, Errors.Error _ => True
  | _, _ => False
  end.
Proof.
  intros.
  unfold Ctypes.field_offset.
  remember 0 as pos; clear Heqpos.
  revert pos; induction m as [| [|] ?]; intros.
  + simpl. auto.
  + simpl. if_tac. auto. apply IHm; auto.
  + inv PLAIN. 
Defined.

Lemma field_type_in_members: forall i m,
  match Ctypes.field_type i m with
  | Errors.Error _ => ~ in_members i m
  | _ => in_members i m
  end.
Proof.
  intros.
  unfold in_members.
  induction m as [| a m].
  + simpl; tauto.
  + simpl.
    if_tac.
    - left; subst; auto.
    - destruct (Ctypes.field_type i m).
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

Lemma complete_legal_cosu_type_field_type: forall id
  (PLAIN: plain_members (co_members (get_co id)) = true)
  i,
  in_members i (co_members (get_co id)) ->
  complete_legal_cosu_type (field_type i (co_members (get_co id))) = true.
Proof.
  unfold get_co.
  intros.
  destruct (cenv_cs ! id) as [co |] eqn:CO.
  + apply in_members_field_type in H; auto.
    pose proof cenv_legal_su _ _ CO.
    apply complete_legal_cosu_member with i (co_members co); eauto.
  + inversion H.
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
  forall m
  (PLAIN: plain_members m = true)
  env i, in_members i m -> Ctypes.field_offset env i m = Errors.OK (field_offset env i m, Full).
Proof.
 unfold field_offset, Ctypes.field_offset.
 intros.
 unfold in_members in H. 
 change 0 with (0*8) at 1.
 generalize 0.
 induction m as [|[|]]; simpl; intros; inv PLAIN. 
 inv H.
 simpl in H.
 if_tac.
 subst.
 f_equal. f_equal.
 unfold bitalignof.
 symmetry.
 apply align_bitalign.
 apply Ctypes.alignof_pos.
 destruct H. congruence. 
 rewrite <- (IHm H1 H); clear IHm.
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
  + inv H. inv H1.
      inversion2 CO H3.
      apply (H6 i (field_type i (co_members co)) (field_offset cenv_cs i (co_members co))); clear H6.
      clear - H0; unfold in_members in H0.
      induction (co_members co).
      * inv H0.
      * simpl in H0|-*. if_tac; auto. subst.
        unfold field_type. simpl. rewrite if_true by auto. auto.
        destruct H0; try congruence. rewrite IHm by auto.
        unfold field_type. simpl. rewrite if_false by auto. auto.
     * apply plain_members_field_offset; auto.
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
  unfold in_members in *.
  destruct (cenv_cs ! id) as [co |] eqn:CO.
  + inv H. inv H1.
      inversion2 CO H3.
      apply (H6 i (field_type i (co_members co))); clear H6.
      clear - H0; unfold in_members in H0.
      induction (co_members co).
      * inv H0.
      * simpl in H0|-*. if_tac; auto. subst.
        unfold field_type. simpl. rewrite if_true by auto. auto.
        destruct H0; try congruence. rewrite IHm by auto.
        unfold field_type. simpl. rewrite if_false by auto. auto.
  + inv H0.
Qed.

Lemma field_offset_aligned: forall i m
  (PLAIN: plain_members m = true),
  (alignof (field_type i m) | field_offset cenv_cs i m).
Proof.
 intros.
 unfold field_offset.
 generalize 0 as pos.
 induction m as [|[|]]; simpl; intros.
 apply Z.divide_1_l.
 unfold field_type. simpl.
 if_tac. subst.
 apply align_divides. apply alignof_pos.
 apply IHm; auto.
 inv PLAIN.
Qed.

Lemma alignof_composite_two_p:
  forall env m, exists n, alignof_composite env m = two_power_nat n.
Proof.
  induction m as [|[|]]; simpl.
- exists 0%nat; auto.
- apply Z.max_case; auto. apply alignof_two_p.
- destruct padding. auto.
   apply Z.max_case; auto.
   apply align_attr_two_p.
   destruct sz.
   exists 0%nat; reflexivity.
   exists 1%nat; reflexivity.
   exists 2%nat; reflexivity.
   exists 0%nat; reflexivity.
Qed.

Lemma alignof_composite_pos:
  forall env m a, align_attr a (alignof_composite env m) > 0.
Proof.
  intros.
  exploit align_attr_two_p. apply (alignof_composite_two_p env m).
  instantiate (1 := a). intros [n EQ].
  rewrite EQ; apply two_power_nat_pos.
Qed.

Lemma alignof_composite_hd_divide: forall a m
  (PLAIN: plain_members (a::m) = true),
 (alignof (type_member a) | alignof_composite cenv_cs (a :: m)).
Proof.
  intros.
  destruct a; try discriminate. simpl type_member.
  destruct (alignof_two_p t) as [N ?].
  destruct (alignof_composite_two_p cenv_cs (Member_plain id t :: m)) as [M ?].
  assert (alignof t <= alignof_composite cenv_cs (Member_plain id t ::m)).
  apply Z.le_max_l.
  fold (alignof t) in *.
  rewrite H in *.
  rewrite H0 in *.
  exact (power_nat_divide N M H1).
Qed.

Lemma alignof_composite_tl_divide: forall a m
  (PLAIN: plain_members (a::m) = true),
   (alignof_composite cenv_cs m | alignof_composite cenv_cs (a :: m)).
Proof.
  intros.
  destruct (alignof_composite_two_p cenv_cs m) as [N ?].
  destruct (alignof_composite_two_p cenv_cs (a :: m)) as [M ?].
  destruct a; try discriminate.
  assert (alignof_composite cenv_cs m <= alignof_composite cenv_cs (Member_plain id t  :: m)) by (apply Z.le_max_r).
  rewrite H in *.
  rewrite H0 in *.
  exact (power_nat_divide N M H1).
Qed.

Lemma alignof_field_type_divide_alignof: forall i m
  (PLAIN: plain_members m = true),
  in_members i m ->
  (alignof (field_type i m) | alignof_composite cenv_cs m).
Proof.
  intros.
  unfold field_type.
  induction m as [| [|] m].
  + inversion H.
  + unfold in_members in H; simpl in H.
    simpl Ctypes.field_type.
    if_tac.
    - apply alignof_composite_hd_divide; auto.
    - eapply Z.divide_trans.
      * apply IHm; auto.
        destruct H; [congruence | auto].
      * apply alignof_composite_tl_divide; auto.
 + discriminate.
Qed.

Fixpoint sizeof_struct (env: composite_env) (cur: Z) (m: members) : Z :=
  match m with
  | nil => cur
  | a :: m' => sizeof_struct env (align cur (@Ctypes.alignof env (type_member a)) + @Ctypes.sizeof env (type_member a)) m'
  end.

Lemma plain_members_sizeof_struct:
  forall (env: composite_env) m 
  (PLAIN: plain_members m = true ), 
  sizeof_struct env 0 m = Ctypes.sizeof_struct env m.
Proof.
intros.
unfold Ctypes.sizeof_struct.
change 0 with (0*8) at 2.
generalize 0.
induction m as [|[|]]; simpl in *; [ | | discriminate]; intros.
unfold bytes_of_bits.
rewrite Z.div_add_l by computable.
change (7/8) with 0. lia. 
rewrite IHm by auto.
f_equal. f_equal.
unfold bitalignof, bitsizeof.
rewrite Z.mul_add_distr_r.
f_equal.
rewrite align_bitalign by apply Ctypes.alignof_pos.
unfold align.
pose proof (Ctypes.alignof_pos t).
forget (Ctypes.alignof t) as a.
replace (z*8+a*8-1) with (z*8-1+a*8) by lia.
forget (z*8-1) as u.
rewrite Z.mul_assoc.
rewrite Z.div_mul by computable.
auto.
Qed.

Lemma sizeof_struct_incr:
  forall env m cur, cur <= sizeof_struct env cur m.
Proof.
  induction m as [|[|]]; intros.
- simpl. lia.
- simpl. apply Z.le_trans with (align cur (@Ctypes.alignof env t)).
  apply align_le. apply Ctypes.alignof_pos.
  apply Z.le_trans with (align cur (@Ctypes.alignof env t) + @Ctypes.sizeof env t).
  generalize (@Ctypes.sizeof_pos env t); lia.
  apply IHm.
- 
  unfold sizeof_struct; fold sizeof_struct.
  simpl type_member.
  set (t := Tint _ _ _).
  apply Z.le_trans with (align cur (@Ctypes.alignof env t)).
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
  intros until ty. induction fld as [|[|]]; intros.
- simpl in *; lia.
- simpl in *.
   destruct (ident_eq id id0).
   subst id0. unfold field_type in H1. simpl in H1. rewrite if_true in H1 by auto. subst.
  split.
  apply align_le. apply Ctypes.alignof_pos. apply sizeof_struct_incr.
  unfold field_type in H1. simpl in H1. rewrite if_false in H1 by auto.
  exploit IHfld; eauto. intros [A B]. split; auto.
  eapply Z.le_trans; try apply A. apply Z.le_trans with (align pos (@Ctypes.alignof env t)).
  apply align_le. apply Ctypes.alignof_pos. generalize (@Ctypes.sizeof_pos env t). lia.
-  unfold field_offset_rec in H0. lia.
Qed.

Lemma in_members_field_offset_pos:
  forall env i m
  (PLAIN: plain_members m = true),
  in_members i m -> 0 <= field_offset env i m.
Proof.
 intros.
 unfold field_offset.
 set (pos:=0) at 2.
 assert (0 <= pos) by lia.
 clearbody pos.
 revert pos H0; induction m as [|[|]]; simpl; intros. inv H.
 if_tac. subst. eapply Z.le_trans. apply H0.
 apply align_le. apply Ctypes.alignof_pos.
 destruct H. simpl in H; subst; contradiction. apply IHm; auto.
 pose proof (Ctypes.alignof_pos t). pose proof (Ctypes.sizeof_pos t).
 apply Z.le_trans with (align pos (Ctypes.alignof t)); try lia.
 eapply Z.le_trans. apply H0.
 apply align_le; auto.
 discriminate.
Qed.

(* if sizeof Tvoid = 0, this lemma can be nicer. *)
Lemma field_offset_in_range: forall i m
  (PLAIN: plain_members m = true),
  in_members i m ->
  0 <= field_offset cenv_cs i m /\ field_offset cenv_cs i m + sizeof (field_type i m) <= sizeof_struct cenv_cs 0 m.
Proof.
  intros.
  pose proof (in_members_field_offset_pos cenv_cs i m PLAIN H).
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
  induction m as [|[|] m].
  + inversion H.
  + simpl.
    if_tac.
    - apply Z.le_max_l.
    - simpl in H; destruct H; [congruence |].
     specialize (IHm H).
     fold (sizeof t).
     pose proof Z.le_max_r (sizeof t) (sizeof_union cenv_cs m).
     lia.
  + simpl.
    if_tac.
    - apply Z.le_max_l.
    - simpl in H; destruct H; [congruence |].
     specialize (IHm H).
     set (t := match Ctypes.field_type i m with
             | Errors.OK t => t
             | Errors.Error _ => Tvoid
             end) in *.
     pose proof Z.le_max_r (sizeof t) (sizeof_union cenv_cs m).
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
  unfold field_type.
  intros until fld. intros G1 G2. unfold field_offset. generalize 0 as pos.
  induction fld as [|[|]]; simpl; intros.
- lia.
- if_tac in H; if_tac in H1.
+ congruence.
+ subst. 
  exploit field_offset_rec_in_range. apply G2. reflexivity. reflexivity. tauto.
+ subst.
  exploit field_offset_rec_in_range. apply G1. reflexivity. reflexivity. tauto.
+ eapply IHfld; eauto.
- subst. lia.
Qed.

(* if sizeof Tvoid = 0, this lemma can be nicer. *)
Lemma field_offset_no_overlap:
  forall i1 i2 m
 (PLAIN: plain_members m = true),
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
  induction m as [| [|] m].
  + reflexivity.
  + simpl in H.
    simpl. if_tac; subst; tauto.
  + simpl in H. simpl. if_tac; subst; tauto.
Qed.

Lemma not_in_members_field_offset: forall i m,
  ~ in_members i m ->
  field_offset cenv_cs i m = -1.
Proof.
  unfold in_members, field_offset, Ctypes.field_offset.
  intros.
  generalize 0 at 1.
  induction m as [| [|] m]; intros.
  + reflexivity.
  + simpl in H.
    simpl. if_tac; subst. tauto. apply IHm. tauto.
  + reflexivity.
Qed.

Lemma field_offset_next_in_range: forall i m
  (PLAIN: plain_members m = true)
  sz,
  in_members i m ->
  sizeof_struct cenv_cs 0 m <= sz ->
  field_offset cenv_cs i m + sizeof (field_type i m) <=
  field_offset_next cenv_cs i m sz <= sz.
Proof.
  intros.
  destruct m as [| [i0 t0|] m]; [inversion H | | discriminate].
  unfold field_offset, Ctypes.field_offset, field_offset_next, field_type.
  pattern 0 at 2 3; replace 0 with (align 0 (alignof t0)) by (apply align_0, alignof_pos).
  match goal with
  | |- ?A => assert (A /\
                     0 <= field_offset_rec cenv_cs i (Member_plain i0 t0 :: m) 0 /\
                     match Ctypes.field_type i (Member_plain i0 t0 :: m) with
                     | Errors.OK _ => True
                     | _ => False
                     end); [| tauto]
  end.
  simpl in PLAIN.
  revert i0 t0 H H0; generalize 0; induction m as [| [i1 t1|] m]; intros; [ | | discriminate].
  + destruct (ident_eq i i0); [| destruct H; simpl in H; try congruence; tauto].
    subst; simpl.
    if_tac; [| congruence].
    simpl in H0.
   fold (sizeof t0) in *.
   split3; auto; try lia. apply align_le, alignof_pos.
  + remember (Member_plain i1 t1 :: m) as m0. simpl in H0 |- *. subst m0.
    destruct (ident_eq i i0).
    - split3; auto.
      split.
      * apply align_le, alignof_pos.
      * pose proof sizeof_struct_incr cenv_cs m (align (align z (alignof t0) + sizeof t0)
            (alignof t1) + sizeof t1).
        pose proof sizeof_pos t1.
        unfold expr.sizeof, expr.alignof in *.
        simpl in H0. simpl type_member. lia.
      * apply align_le, alignof_pos.      
    - destruct H as [H | H]; [simpl in H; congruence |].
      specialize (IHm PLAIN (align z (alignof t0) + sizeof t0) i1 t1 H H0).
        unfold expr.sizeof, expr.alignof in *.
      destruct IHm as [? [? ?]]. split3; try tauto.
      eapply Z.le_trans; [ | apply H2].
      pose proof (align_le z (Ctypes.alignof t0) (alignof_pos _)). pose proof (Ctypes.sizeof_pos t0). lia.
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
  | a :: m0 => ~ in_members (name_member a) m0 /\ members_no_replicate m0 = true
  end.
Proof.
  intros.
  unfold members_no_replicate.
  destruct m; simpl.
  + assert (true = true) by auto; tauto.
  + destruct (id_in_list (name_member m) (map name_member m0)) eqn:HH.
    - apply id_in_list_true in HH.
       split; intros. inv H.  destruct H. exfalso; apply H.
      apply HH.
    - apply id_in_list_false in HH.
      split; intros. split; auto. destruct H; auto.
Defined.

Fixpoint get_member (i: ident) (m: members) : member :=
 match m with
  | a::m' => if ident_eq i (name_member a) then a else get_member i m'
  | nil => Member_plain i Ctypes.Tvoid
  end.

Lemma name_member_get:
  forall i m, name_member (get_member i m) = i.
Proof.
induction m; simpl; auto.
if_tac; auto.
Defined.

Lemma map_members_ext: forall A (f f':member -> A) (m: list member),
  members_no_replicate m = true ->
  (forall i, in_members i m -> f (get_member i m)= f' (get_member i m)) ->
  map f m = map f' m.
Proof.
  intros.
  induction m as [| a0 m].
  + reflexivity.
  + simpl.
    rewrite members_no_replicate_ind in H.
    f_equal.
    - specialize (H0 (name_member a0)).
      unfold field_type, in_members in H0.
      simpl in H0; if_tac in H0; [| congruence].
      apply H0; auto.
    - apply IHm. tauto.
      intros.
      specialize (H0 i).
      unfold in_members in H0.
      simpl in H0; if_tac in H0; [subst; tauto |].
      apply H0; auto.
Defined.

Lemma in_plain_members: forall a m (PLAIN: plain_members m = true),
   In a m -> 
   a = Member_plain (name_member a) (type_member a).
Proof.
 induction m as [|[|]]; simpl; intros.
 contradiction.
 destruct H. subst. reflexivity.
 auto.
 inv PLAIN.
Qed.

Lemma plain_members_union_field_offset:
  forall m (PLAIN: plain_members m = true) 
   env i, in_members i m -> union_field_offset env i m = Errors.OK (0, Full).
Proof.
 unfold union_field_offset, Ctypes.union_field_offset.
 intros.
 unfold in_members in H.
 induction m as [|[|]]; simpl; intros; [ | | discriminate].
 - 
 inv H.
 -
 simpl in H.
 if_tac.
 subst.
 f_equal. f_equal. rewrite align_0. reflexivity.
 unfold bitalignof. pose proof (Ctypes.alignof_pos t); lia.
 destruct H. congruence. 
 rewrite <- (IHm PLAIN H); clear IHm.
 f_equal.
Qed.

Lemma in_members_tail_no_replicate: forall i a m,
  members_no_replicate (a :: m) = true ->
  in_members i m ->
  i <> name_member a.
Proof.
  intros.
 destruct (members_no_replicate_ind (a::m)) as [? _].
 apply H1 in H. clear H1.
  intro.
  subst. destruct H. auto.
Defined.

Lemma neq_field_offset_rec_cons: forall env i a m
 (PLAIN: plain_members (a::m) = true) z,
  i <> name_member a  ->
  field_offset_rec env i (a :: m) z =
  field_offset_rec env i m (align z (Ctypes.alignof (type_member a)) + Ctypes.sizeof (type_member a)).
Proof.
  intros.
  destruct a; try discriminate.
  simpl in *.
  if_tac; [congruence |].
  auto.
Qed.

Lemma neq_field_offset_next_rec_cons: forall env i a0 a1 m
 (PLAIN: plain_members (a0::a1::m) = true) z sz,
  i <> name_member a0 ->
  field_offset_next_rec env i (a0::a1:: m) z sz =
  field_offset_next_rec env i (a1 :: m) (align (z +  Ctypes.sizeof (type_member a0)) (Ctypes.alignof (type_member a1))) sz.
Proof.
  intros.
  destruct a0; try discriminate; simpl in PLAIN.
  destruct a1; try discriminate; simpl in PLAIN.
  simpl. simpl in H.
  if_tac; [congruence |].
  auto.
Qed.

Lemma sizeof_struct_0: forall env i m
 (PLAIN: plain_members m = true),
  sizeof_struct env 0 m = 0 ->
  in_members i m ->
  Ctypes.sizeof (field_type i m) = 0 /\
  field_offset_next env i m 0 - (field_offset env i m + Ctypes.sizeof (field_type i m)) = 0.
Proof.
  intros.
  unfold field_type, field_offset, Ctypes.field_offset, field_offset_next.
  induction m as [| [i0 t0|] m]; [ | | discriminate].
  + inversion H0.
  + simpl in H,PLAIN.
    pose proof sizeof_struct_incr env m (align 0 (Ctypes.alignof t0) + Ctypes.sizeof t0).
    pose proof align_le 0 (Ctypes.alignof t0) (Ctypes.alignof_pos _).
    pose proof Ctypes.sizeof_pos t0.
    destruct (ident_eq i i0).
    - simpl in *.
      if_tac; [| congruence].
      replace (Ctypes.sizeof t0) with 0 by lia.
      destruct m as [| [? ?|] m]; try discriminate;
      rewrite !align_0 by apply Ctypes.alignof_pos;
      lia.
    - destruct H0; [simpl in H0; congruence |].
      simpl.
      if_tac; [congruence |].
      replace (Ctypes.sizeof t0) with 0 by lia.
      destruct m as [| [? ?|] m]; [inversion H0 | | discriminate].
      rewrite !align_0 by apply Ctypes.alignof_pos.
      apply (IHm PLAIN); [| auto].
      replace (align 0 (Ctypes.alignof t0) + Ctypes.sizeof t0) with 0 in * by lia.
      auto.
Qed.

Lemma sizeof_union_pos:
  forall env m, 0 <= sizeof_union env m.
Proof.
  induction m as [|[|]]; simpl; extlia.
Qed.

Lemma sizeof_union_0: forall env i m,
  sizeof_union env m = 0 ->
  in_members i m ->
  Ctypes.sizeof (field_type i m) = 0.
Proof.
  intros. unfold field_type, in_members in *. 
  induction m as [| [i0 t0|] m].
  + inversion H0.
  + simpl in *.
     if_tac.
    - 
      pose proof Ctypes.sizeof_pos t0.
      pose proof Z.le_max_l (Ctypes.sizeof t0) (sizeof_union env m).
      lia.
    - destruct H0; [congruence |].
      simpl.
      apply IHm; [| auto].
      pose proof sizeof_union_pos env m.
      pose proof Z.le_max_r (Ctypes.sizeof t0) (sizeof_union env m).
      lia.
  + simpl in *.
    exfalso; clear - H. destruct sz; lia.
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
  field_type (name_member it) m = type_member it.
Proof.
  unfold field_type.
  intros.
  induction m as [|[|]].
  + inversion H0.
  + 
    simpl.
     if_tac.
    - destruct H0; [inversion H0; auto |].
      apply in_map with (f := name_member) in H0.
      pose proof in_members_tail_no_replicate _ _ _ H H0.
      contradiction H1; auto.
    - apply IHm.
       destruct (members_no_replicate_ind (Member_plain id t ::m)) as [? _].
       destruct (H2 H); auto.
      * inversion H0; [| auto].
        subst. contradiction H1; auto.
  + 
    simpl.
     if_tac.
    - destruct H0; [inversion H0; auto |].
      apply in_map with (f := name_member) in H0.
      pose proof in_members_tail_no_replicate _ _ _ H H0.
      contradiction H1; auto.
    - apply IHm.
       destruct (members_no_replicate_ind (Member_bitfield id sz sg a width padding ::m)) as [? _].
       destruct (H2 H); auto.
      * inversion H0; [| auto].
        subst. contradiction H1; auto.
Defined.

End COMPOSITE_ENV.

Lemma members_spec_change_composite' {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: 
  forall id,
  match (coeq cs_from cs_to) ! id with
  | Some b => test_aux cs_from cs_to b id
  | None => false
  end = true ->
  Forall (fun it => cs_preserve_type cs_from cs_to (coeq _ _) (type_member it) = true) 
             (co_members (@get_co cs_to id)).
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
    unfold get_co in *.
    rewrite H0 in *.
    clear - H1.
    symmetry in H1.
    induction (co_members c) as [|[|]]; intros.
    - constructor.
    - 
       simpl in H1; rewrite andb_true_iff in H1; destruct H1.
      constructor; auto.
   - 
       simpl in H1.
      constructor; auto.
  + destruct ((coeq cs_from cs_to) ! id) eqn:?H.
    - pose proof proj2 (coeq_complete _ _ id) (ex_intro _ b H1) as [co ?].
      congruence.
    - inv H.
Qed.

Lemma members_spec_change_composite'' {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}:
  forall id,
  match (coeq cs_from cs_to) ! id with
  | Some b => test_aux cs_from cs_to b id
  | None => false
  end = true ->
  forall i, cs_preserve_type cs_from cs_to (coeq _ _) (field_type i (co_members (@get_co cs_to id))) = true.
Proof.
  intros.
  apply (@members_spec_change_composite' cs_from cs_to _ _) in H.
  induction H as [|[??|]]; auto.
  unfold field_type;
  simpl; if_tac; auto.
  unfold field_type;
  simpl; if_tac; auto.
Qed.
 
Lemma members_spec_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}:
  forall id,
  match (coeq cs_from cs_to) ! id with
  | Some b => test_aux cs_from cs_to b id
  | None => false
  end = true ->
  Forall (fun it => cs_preserve_type cs_from cs_to (coeq _ _) (field_type (name_member it) (co_members (@get_co cs_to id))) = true) (co_members (@get_co cs_to id)).
Proof.
  intros.
  apply (members_spec_change_composite' _) in H.
  assert (Forall (fun it: member => field_type (name_member it) (co_members (@get_co cs_to id)) = type_member it) (co_members (@get_co cs_to id))).
  1:{
    rewrite Forall_forall.
    intros it ?.
    apply In_field_type; auto.
    apply get_co_members_no_replicate.
  }
  revert H0.
 generalize  (co_members (get_co id)) at 1 3.
  induction H as [| [i t|] ?]; constructor.
  + inv H1.
    simpl in *.
    rewrite H4; auto.
  + inv H1. 
    auto.
  + inv H1. simpl in H4|-*. rewrite H4. auto. 
  + inv H1.  auto.
Qed.


(* TODO: we have already proved a related field_offset lemma in veric/change_compspecs.v. But it seems not clear how to use that in an elegant way. *)
Lemma field_offset_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: 
  forall id i,
  match (coeq cs_from cs_to) ! id with
  | Some b => test_aux cs_from cs_to b id
  | None => false
  end = true ->
  field_offset (@cenv_cs cs_from) i (co_members (@get_co cs_to id)) =
  field_offset (@cenv_cs cs_to) i (co_members (@get_co cs_to id)).
Proof.
  intros.
  apply (members_spec_change_composite' _) in H.
  unfold field_offset.
  generalize 0.
  induction (co_members (@get_co cs_to id)) as [| [i0 t0|] ?]; intros.
  + auto.
  + simpl.
    inv H.
    if_tac.
    - f_equal.
      apply alignof_change_composite; auto.
    - specialize (IHm  H3).
       fold (@alignof cs_from t0) in *. fold (@sizeof cs_from t0) in *.
       fold (@alignof cs_to t0) in *. fold (@sizeof cs_to t0) in *.
      rewrite alignof_change_composite, sizeof_change_composite by auto.
      apply IHm.
  + reflexivity.
Qed.

Lemma field_offset_next_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: 
  forall id i,
  match (coeq cs_from cs_to) ! id with
  | Some b => test_aux cs_from cs_to b id
  | None => false
  end = true ->
  field_offset_next (@cenv_cs cs_from) i (co_members (@get_co cs_to id)) (co_sizeof (@get_co cs_from id)) =
  field_offset_next (@cenv_cs cs_to) i (co_members (@get_co cs_to id)) (co_sizeof (@get_co cs_to id)).
Proof.
  intros.
  rewrite co_sizeof_get_co_change_composite by auto.
  apply (members_spec_change_composite' _) in H.
  unfold field_offset_next.
  generalize 0.
  destruct H as [| [i0 t0|] ? ]; intros; auto.
  simpl in H, H0.
  revert i0 t0 H z.
  induction H0 as [| [i1 t1|] ? ]; intros.
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
  + simpl. if_tac; auto. 
      fold (@sizeof cs_from t0) in *.
      fold (@sizeof cs_to t0) in *.
      rewrite (sizeof_change_composite t0) by auto.
      auto.
Qed.

Arguments field_type i m / .
Arguments field_offset env i m / .

