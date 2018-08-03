Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.type_induction.
Require Import VST.floyd.nested_pred_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require VST.floyd.aggregate_pred. Import VST.floyd.aggregate_pred.aggregate_pred.
Import VST.floyd.aggregate_pred.auxiliary_pred.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.jmeq_lemmas.
Require Import VST.floyd.sublist.
Require Export VST.floyd.fieldlist.
Require Export VST.floyd.aggregate_type.

Opaque alignof.

Local Open Scope logic.

Arguments align !n !amount / .
Arguments Z.max !n !m / .

Definition offset_in_range ofs p :=
  match p with
  | Vptr b iofs => 0 <= Ptrofs.unsigned iofs + ofs <= Ptrofs.modulus
  | _ => True
  end.

Definition offset_strict_in_range ofs p :=
  match p with
  | Vptr b iofs => 0 <= Ptrofs.unsigned iofs + ofs < Ptrofs.modulus
  | _ => True
  end.

(************************************************

Definition of data_at_rec

Always assume in arguments of data_at_rec has argument pos with alignment criterion.

************************************************)

Section CENV.

Context {cs: compspecs}.

(*
Lemma proj_struct_default: forall i m d,
  in_members i m ->
  members_no_replicate m = true ->
  proj_struct i m (struct_default_val m) d = default_val (field_type i m).
Proof.
Qed.

Lemma proj_union_default: forall i m d,
  i = fst (members_union_inj (union_default_val m)) ->
  m <> nil ->
  members_no_replicate m = true ->
  proj_union i m (union_default_val m) d = default_val (field_type2 i m).
Proof.
  unfold field_type2.
  intros.
  destruct m as [| (i0, t0) m]; [congruence |].
  destruct m as [| (i1, t1) m].
  + simpl in d, H |- *; subst.
    if_tac; [| congruence].
    unfold eq_rect_r; rewrite <- eq_rect_eq; auto.
  + simpl in H; subst.
    simpl in d |- *; subst.
    if_tac; [| congruence].
    unfold eq_rect_r; rewrite <- eq_rect_eq; auto.
Qed.
*)
Section WITH_SHARE.

Variable sh: share.

Definition data_at_rec: forall t, reptype t -> val -> mpred :=
  type_func (fun t => reptype t -> val -> mpred)
    (fun t v p =>
       if type_is_volatile t
       then memory_block sh (sizeof t) p
       else mapsto sh t p (repinject t v))
    (fun t n a P v => array_pred 0 (Z.max 0 n) (fun i v => at_offset (P v) (sizeof t * i)) (unfold_reptype v))
    (fun id a P v => struct_data_at_rec_aux sh (co_members (get_co id)) (co_members (get_co id)) (co_sizeof (get_co id)) P (unfold_reptype v))
    (fun id a P v => union_data_at_rec_aux sh (co_members (get_co id)) (co_members (get_co id)) (co_sizeof (get_co id)) P (unfold_reptype v)).

Lemma data_at_rec_eq: forall t v,
  data_at_rec t v =
  match t return REPTYPE t -> val -> mpred with
  | Tvoid
  | Tfunction _ _ _ => fun _ _ => FF
  | Tint _ _ _
  | Tfloat _ _
  | Tlong _ _
  | Tpointer _ _ => fun v p =>
                      if type_is_volatile t
                      then memory_block sh (sizeof t) p
                      else mapsto sh t p v
  | Tarray t0 n a => array_pred 0 (Z.max 0 n) (fun i v => at_offset (data_at_rec t0 v) (sizeof t0 * i))
  | Tstruct id a => struct_pred (co_members (get_co id))
                      (fun it v => withspacer sh
                        (field_offset cenv_cs (fst it) (co_members (get_co id)) + sizeof (field_type (fst it) (co_members (get_co id))))
                        (field_offset_next cenv_cs (fst it) (co_members (get_co id)) (co_sizeof (get_co id)))
                        (at_offset (data_at_rec (field_type (fst it) (co_members (get_co id))) v) (field_offset cenv_cs (fst it) (co_members (get_co id)))))
  | Tunion id a => union_pred (co_members (get_co id))
                     (fun it v => withspacer sh
                      (sizeof (field_type (fst it) (co_members (get_co id))))
                      (co_sizeof (get_co id))
                      (data_at_rec (field_type (fst it) (co_members (get_co id))) v))
  end (unfold_reptype v).
Proof.
  intros.
  unfold data_at_rec at 1.
  rewrite type_func_eq.
  destruct t; auto;
  try solve [destruct (readable_share_dec sh); reflexivity];
  try solve [
  match goal with
  | |- context[repinject ?tt] =>
    rewrite (repinject_unfold_reptype tt); auto
  end].
  + rewrite <- struct_data_at_rec_aux_spec; reflexivity.
  + rewrite <- union_data_at_rec_aux_spec; reflexivity.
Qed.

End WITH_SHARE.

Lemma data_at_rec_type_changable: forall (sh: Share.t) (t1 t2: type) v1 v2,
  t1 = t2 ->
  JMeq v1 v2 ->
  data_at_rec sh t1 v1 = data_at_rec sh t2 v2.
Proof.
  intros.
  subst t2.
  apply JMeq_eq in H0.
  rewrite H0.
  reflexivity.
Qed.
(*
Lemma data_at_type_changable: forall (sh: Share.t) (t1 t2: type) v1 v2,
  t1 = t2 ->
  JMeq v1 v2 ->
  data_at sh t1 v1 = data_at sh t2 v2.
Proof.
  intros.
  unfold data_at.
  simpl. extensionality.
  erewrite data_at_rec_type_changable; [| exact H| exact H0].
  rewrite H.
  reflexivity.
Qed.
*)
Lemma by_value_default_val: forall t:type,
  type_is_by_value t = true -> JMeq (default_val t) Vundef.
Proof.
  intros.
  destruct t; try inversion H; try tauto; apply JMeq_refl.
Qed.

(************************************************

Transformation between data_at/data_at_ and mapsto.

************************************************)

Lemma by_value_reptype: forall t, type_is_by_value t = true -> reptype t = val.
Proof.
  intros.
  destruct t; simpl in H; try inversion H; tauto.
Qed.

Lemma by_value_data_at_rec_volatile: forall sh t v p,
  type_is_by_value t = true ->
  type_is_volatile t = true ->
  data_at_rec sh t v p = memory_block sh (sizeof t) p.
Proof.
  intros.
  rewrite data_at_rec_eq; destruct t; try solve [inversion H];
  match goal with
  | |- context[type_is_volatile ?tt] =>
    destruct (type_is_volatile tt) eqn:HH; auto;
    rewrite <- (repinject_unfold_reptype tt); auto
  end;
  inversion H0.
Qed.

Lemma by_value_data_at_rec_nonvolatile: forall sh t v p,
  type_is_by_value t = true ->
  type_is_volatile t = false ->
  data_at_rec sh t v p = mapsto sh t p (repinject t v).
Proof.
  intros.
  rewrite data_at_rec_eq; destruct t; try solve [inversion H]; rewrite H0;
  match goal with
  | |- context[repinject ?tt] =>
    rewrite (repinject_unfold_reptype tt); auto
  end.
Qed.

Lemma by_value_data_at_rec_default_val: forall sh t p,
  type_is_by_value t = true ->
  size_compatible t p ->
  align_compatible t p ->
  data_at_rec sh t (default_val t) p = memory_block sh (sizeof t) p.
Proof.
  intros.
  destruct (type_is_volatile t) eqn:?H.
  + apply by_value_data_at_rec_volatile; auto.
  + rewrite data_at_rec_eq; destruct t; try solve [inversion H]; rewrite H2;
    symmetry;
    rewrite memory_block_mapsto_ by auto; unfold mapsto_;
    try rewrite if_true by auto; auto.
Qed.

Lemma by_value_data_at_rec_nonreachable: forall sh t p v,
  type_is_by_value t = true ->
  size_compatible t p ->
  align_compatible t p ->
  ~ readable_share sh ->
  tc_val' t (repinject t v) ->
  data_at_rec sh t v p = memory_block sh (sizeof t) p.
Proof.
  intros.
  destruct (type_is_volatile t) eqn:?H.
  + apply by_value_data_at_rec_volatile; auto.
  + rewrite by_value_data_at_rec_nonvolatile by auto.
    symmetry;
    apply nonreadable_memory_block_mapsto; auto.
Qed.

Lemma by_value_data_at_rec_default_val2: forall sh t b ofs,
  type_is_by_value t = true ->
  0 <= ofs /\ ofs + sizeof t < Ptrofs.modulus ->
  align_compatible_rec cenv_cs t ofs ->
  data_at_rec sh t (default_val t) (Vptr b (Ptrofs.repr ofs)) =
  memory_block sh (sizeof t) (Vptr b (Ptrofs.repr ofs)).
Proof.
  intros.
  apply by_value_data_at_rec_default_val; auto.
  + unfold size_compatible.
    solve_mod_modulus.
    pose_mod_le ofs.
    omega.
  + unfold align_compatible.
    solve_mod_modulus.
    pose proof sizeof_pos t.
    rewrite Zmod_small by omega.
    auto.
Qed.

Lemma by_value_data_at_rec_nonreachable2: forall sh t b ofs v,
  type_is_by_value t = true ->
  0 <= ofs /\ ofs + sizeof t < Ptrofs.modulus ->
  align_compatible_rec cenv_cs t ofs ->
  ~ readable_share sh ->
  tc_val' t (repinject t v) ->
  data_at_rec sh t v (Vptr b (Ptrofs.repr ofs)) = memory_block sh (sizeof t) (Vptr b (Ptrofs.repr ofs)).
Proof.
  intros.
  apply by_value_data_at_rec_nonreachable; auto.
  + unfold size_compatible.
    solve_mod_modulus.
    pose_mod_le ofs.
    omega.
  + unfold align_compatible.
    solve_mod_modulus.
    pose proof sizeof_pos t.
    rewrite Zmod_small by omega.
    auto.
Qed.

(*
Lemma by_value_data_at_: forall sh t p,
  type_is_by_value t = true ->
  data_at_ sh t p = !! field_compatible t nil p && mapsto_ sh t p.
Proof.
  intros.
  unfold data_at_, mapsto_.
  destruct t; simpl in H; try inversion H; try tauto; simpl default_val;
  apply by_value_data_at; reflexivity.
Qed.
*)

(************************************************

Transformation between data_at and data_at_rec. This is used in transformation
between field_at and data_at.

************************************************)

Lemma lower_sepcon_val':
  forall (P Q: val->mpred) v,
  ((P*Q) v) = (P v * Q v).
Proof. reflexivity. Qed.

(*
Lemma unsigned_add: forall i pos, 0 <= pos -> Int.unsigned (Int.add i (Int.repr pos)) = (Int.unsigned i + pos) mod Int.modulus.
Proof.
  intros.
  unfold Int.add.
  pose proof Int.modulus_pos.
  pose proof Int.unsigned_range i.
  pose proof Int.unsigned_range (Int.repr pos).
  rewrite !Int.unsigned_repr_eq in *.
  rewrite Z.add_mod by omega.
  rewrite Z.mod_mod by omega.
  rewrite <- Z.add_mod by omega.
  reflexivity.
Qed.

Lemma memory_block_data_at__aux1: forall i pos t,
  0 <= pos /\ pos + sizeof t <= Int.modulus - Int.unsigned i ->
  Int.unsigned (Int.add i (Int.repr pos)) + sizeof t <= Int.modulus.
Proof.
  intros.
  destruct H.
  rewrite (unsigned_add i pos H).
  cut ((Int.unsigned i + pos) mod Int.modulus <= Int.unsigned i + pos).
    { intros. omega. }
  pose proof Int.modulus_pos.
  pose proof Int.unsigned_range i.
  apply Z.mod_le; omega.
Qed.

Lemma memory_block_data_at__aux2: forall i pos t,
  0 <= pos /\ pos + sizeof t <= Int.modulus - Int.unsigned i ->
  (alignof t | Int.unsigned i) ->
  (alignof t | pos) ->
  (alignof t | Int.unsigned (Int.add i (Int.repr pos))).
Proof.
  intros.
  destruct H.
  rewrite (unsigned_add i pos H).
  destruct (zlt (Int.unsigned i + pos) Int.modulus).
  + pose proof Int.unsigned_range i.
    rewrite Z.mod_small by omega.
    apply Z.divide_add_r; assumption.
  + pose proof sizeof_pos cenv_cs t.
    assert (Int.unsigned i + pos = Int.modulus) by omega.
    rewrite H4.
    rewrite Z_mod_same_full.
    apply Z.divide_0_r.
Qed.
*)
Lemma Znth_nil: forall {A}{d: Inhabitant A} n, Znth n nil = default.
Proof.
  intros.
  unfold Znth.
  if_tac; auto.
  simpl.
  destruct (Z.to_nat n); auto.
Qed.

Lemma offset_val_zero_Vptr: forall b i, offset_val 0 (Vptr b i) = Vptr b i.
Proof.
  intros.
  unfold offset_val, Ptrofs.add.
  change (Ptrofs.unsigned (Ptrofs.repr 0)) with 0.
  rewrite Z.add_0_r.
  rewrite Ptrofs.repr_unsigned.
  reflexivity.
Qed.
(*
Ltac AUTO_IND :=
  match goal with
  | H: complete_legal_cosu_type (Tarray ?t ?n ?a) = true |- complete_legal_cosu_type ?t = true =>
    simpl in H; auto
  | H: (alignof (Tarray ?t ?z ?a) | ?ofs)
    |- (alignof ?t | ?ofs + _) =>
    apply Z.divide_add_r;
    [ eapply Z.divide_trans; [eapply alignof_divide_alignof_Tarray |]; eauto
    | apply Z.divide_mul_l; eapply legal_alignas_type_Tarray; eauto]
  | H: legal_alignas_type (Tstruct ?id ?a) = true |-
    legal_alignas_type (field_type ?i (co_members (get_co ?id))) = true =>
    unfold legal_alignas_type in H;
    apply nested_pred_Tstruct2 with (i0 := i) in H;
    [exact H | auto]
  | H: legal_cosu_type (Tstruct ?id ?a) = true |-
    legal_cosu_type (field_type ?i (co_members (get_co ?id))) = true =>
    unfold legal_cosu_type in H;
    apply nested_pred_Tstruct2 with (i0 := i) in H;
    [exact H | auto]
  | |- complete_type ?env (field_type ?i (co_members (get_co ?id))) = true =>
    apply complete_type_field_type; auto
  | H: (alignof (Tstruct ?id ?a) | ?ofs)
    |- (alignof (field_type ?i (co_members (get_co ?id))) | ?ofs + _) =>
    apply Z.divide_add_r;
    [ eapply Z.divide_trans; [apply alignof_field_type_divide_alignof; auto |];
      eapply Z.divide_trans; [apply legal_alignas_type_Tstruct; eauto | auto]
    | apply field_offset_aligned]
  | H: legal_alignas_type (Tunion ?id ?a) = true |-
    legal_alignas_type (field_type ?i (co_members (get_co ?id))) = true =>
    unfold legal_alignas_type in H;
    apply nested_pred_Tunion2 with (i0 := i) in H;
    [exact H | auto]
  | H: legal_cosu_type (Tunion ?id ?a) = true |-
    legal_cosu_type (field_type ?i (co_members (get_co ?id))) = true =>
    unfold legal_cosu_type in H;
    apply nested_pred_Tunion2 with (i0 := i) in H;
    [exact H | auto]
  | H: (alignof (Tunion ?id ?a) | ?ofs)
    |- (alignof (field_type ?i (co_members (get_co ?id))) | ?ofs) =>
    eapply Z.divide_trans; [apply alignof_field_type_divide_alignof; auto |];
    eapply Z.divide_trans; [apply legal_alignas_type_Tunion; eauto | auto]
  end.
*)

Lemma nth_list_repeat: forall A i n (x :A),
    nth i (list_repeat n x) x = x.
Proof.
 induction i; destruct n; simpl; auto.
Qed.

Lemma nth_list_repeat': forall A i n (x y :A),
    (i < n)%nat ->
    nth i (list_repeat n x) y = x.
Proof.
 induction i; destruct n; simpl; intros; auto.
 omega. omega.
 apply IHi; auto. omega.
Qed.

 Lemma Z2Nat_max0: forall z, Z.to_nat (Z.max 0 z) = Z.to_nat z.
 Proof.
  intros.
  rewrite Z.max_comm, <- nat_of_Z_max, Nat2Z.id.
  auto.
Qed.

Lemma range_max0: forall x z, 0 <= x < Z.max 0 z <-> 0 <= x < z.
Proof.
  intros.
  destruct (zlt z 0).
  + rewrite Z.max_l by omega.
    omega.
  + rewrite Z.max_r by omega.
    omega.
Qed.
  
(* We use (Vptr b (Int.repr ofs)) instead of p because size_compatible is more  *)
(* difficult to use than simple arithmetic in induction proof.                  *)
Lemma memory_block_data_at_rec_default_val: forall sh t b ofs
  (LEGAL_COSU: complete_legal_cosu_type t = true),
  0 <= ofs /\ ofs + sizeof t < Ptrofs.modulus ->
  align_compatible_rec cenv_cs t ofs ->
  data_at_rec sh t (default_val t) (Vptr b (Ptrofs.repr ofs)) =
    memory_block sh (sizeof t) (Vptr b (Ptrofs.repr ofs)).
Proof.
  intros sh t.
  type_induction t; intros;
  try solve [inversion COMPLETE];
  try solve [apply by_value_data_at_rec_default_val2; auto];
  rewrite data_at_rec_eq.
  + rewrite (default_val_eq (Tarray t z a)).
    rewrite unfold_fold_reptype.
    rewrite array_pred_ext with
     (P1 := fun i _ p => memory_block sh (sizeof t)
                          (offset_val (sizeof t * i) p))
     (v1 := list_repeat (Z.to_nat (Z.max 0 z)) (default_val t));
     auto.
    rewrite memory_block_array_pred; auto.
    - apply Z.le_max_l.
    - f_equal.
      f_equal.
      rewrite Z2Nat_max0; auto.
    - intros.
      rewrite at_offset_eq3.
      unfold offset_val; solve_mod_modulus.
      unfold Znth. rewrite if_false by omega.
      rewrite nth_list_repeat.
      unfold sizeof in H, H1; fold @sizeof in H,H1.
      pose_size_mult cenv_cs t (0 :: i :: i + 1 :: Z.max 0 z :: nil).
      assert (sizeof t = 0 -> sizeof t * i = 0)%Z by (intros HH; rewrite HH, Z.mul_0_l; auto).
      apply IH; auto; try omega.
      eapply align_compatible_rec_Tarray_inv; [eassumption |].
      apply range_max0; auto.
  + rewrite default_val_eq.
    rewrite unfold_fold_reptype.
    rewrite struct_pred_ext with
     (P1 := fun it _ p =>
              memory_block sh
               (field_offset_next cenv_cs (fst it) (co_members (get_co id)) (co_sizeof (get_co id)) -
                  field_offset cenv_cs (fst it) (co_members (get_co id)))
               (offset_val (field_offset cenv_cs (fst it) (co_members (get_co id))) p))
     (v1 := (struct_default_val (co_members (get_co id))));
    [| apply get_co_members_no_replicate |].
    - rewrite memory_block_struct_pred.
      * rewrite sizeof_Tstruct; auto.
      * apply get_co_members_nil_sizeof_0.
      * apply get_co_members_no_replicate.
      * rewrite sizeof_Tstruct in H.
        pose proof co_consistent_sizeof cenv_cs (get_co id) (get_co_consistent id).
        erewrite complete_legal_cosu_type_Tstruct in H1 by eauto.
        pose proof co_consistent_sizeof cenv_cs (get_co id) (get_co_consistent id).
        unfold sizeof_composite in H1.
        revert H1; pose_align_le; intros; omega.
      * rewrite sizeof_Tstruct in H.
        omega.
    - intros.
      pose proof get_co_members_no_replicate id as NO_REPLI.
      rewrite withspacer_spacer.
      simpl @fst.
      rewrite spacer_memory_block by (simpl; auto).
      rewrite at_offset_eq3.
      unfold offset_val; solve_mod_modulus.
      unfold struct_default_val.
      unfold proj_struct.
      rewrite compact_prod_proj_gen by (apply in_members_field_type; auto).
      rewrite Forall_forall in IH.
      specialize (IH (i, field_type i (co_members (get_co id)))).
      spec IH; [apply in_members_field_type; auto |].
      unfold snd in IH.
      rewrite IH.
      * rewrite Z.add_assoc, sepcon_comm, <- memory_block_split by (pose_field; omega).
        f_equal; omega.
      * apply complete_legal_cosu_type_field_type.
        auto.
      * simpl fst. pose_field; omega.
      * simpl fst. eapply align_compatible_rec_Tstruct_inv'; eauto.
  + assert (co_members (get_co id) = nil \/ co_members (get_co id) <> nil)
      by (destruct (co_members (get_co id)); [left | right]; congruence).
    destruct H1.
    - rewrite sizeof_Tunion.
      rewrite (get_co_members_nil_sizeof_0 _ H1).
      generalize (unfold_reptype (default_val (Tunion id a)));
      rewrite H1 in *;
      intros.
      simpl.
      rewrite memory_block_zero.
      normalize.
    - rewrite default_val_eq.
      rewrite unfold_fold_reptype.
      rewrite union_pred_ext with
       (P1 := fun it _ => memory_block sh (co_sizeof (get_co id)))
       (v1 := (union_default_val (co_members (get_co id))));
      [| apply get_co_members_no_replicate | reflexivity |].
      * rewrite memory_block_union_pred by (apply get_co_members_nil_sizeof_0).
        rewrite sizeof_Tunion.
        auto.
      * intros.
        pose proof get_co_members_no_replicate id as NO_REPLI.
        pose proof @compact_sum_inj_in _ _ (co_members (get_co id)) (union_default_val (co_members (get_co id))) _ _ H3.
        apply in_map with (f := fst) in H4; unfold fst in H4.
        rewrite withspacer_spacer.
        simpl @fst.
        rewrite spacer_memory_block by (simpl; auto).
        unfold offset_val; solve_mod_modulus.
        unfold union_default_val.
        unfold proj_union.
        unfold members_union_inj in *.
        rewrite compact_sum_proj_gen; [| auto].
        rewrite Forall_forall in IH.
        specialize (IH (i, field_type i (co_members (get_co id)))).
        spec IH; [apply in_members_field_type; auto |].
        unfold snd in IH.
        rewrite IH.
        {
          rewrite sepcon_comm, <- memory_block_split by (pose_field; omega).
          f_equal; f_equal; omega.
        } {
          apply complete_legal_cosu_type_field_type.
          auto.
        } {
          pose_field; omega.
        } {
          simpl fst. eapply align_compatible_rec_Tunion_inv'; eauto.
        }
Qed.

(*
Lemma align_1_memory_block_data_at_: forall (sh : share) (t : type),
  legal_alignas_type t = true ->
  nested_legal_fieldlist t = true ->
  nested_non_volatile_type t = true ->
  alignof t = 1%Z ->
  (sizeof t < Ptrofs.modulus)%Z ->
  memory_block sh (Ptrofs.repr (sizeof t)) = data_at_ sh t.
Proof.
  intros.
  extensionality p.
  rewrite data_at__memory_block by auto.
  rewrite andp_comm.
  apply add_andp.
  normalize.
  apply prop_right.
  unfold align_compatible.
  rewrite H2.
  destruct p; auto.
  split; [| auto].
  apply Z.divide_1_l.
Qed.

*)

(*
Lemma data_at_rec_readable:
  forall sh t v p, data_at_rec sh t v p |-- !! readable_share sh.
Proof.
intros sh t.
type_induction t; intros;
rewrite data_at_rec_eq; try apply FF_left.
if_tac.
+ simpl. destruct i; simpl.
rewrite memory_block_eq.
saturate_local.
simpl.
*)

Lemma data_at_rec_data_at_rec_ : forall sh t v b ofs
  (LEGAL_COSU: complete_legal_cosu_type t = true),
  0 <= ofs /\ ofs + sizeof t < Ptrofs.modulus ->
  align_compatible_rec cenv_cs t ofs ->
  data_at_rec sh t v (Vptr b (Ptrofs.repr ofs)) |-- data_at_rec sh t (default_val t) (Vptr b (Ptrofs.repr ofs)).
Proof.
  intros sh t.
  type_induction t; intros;
  try solve [inversion LEGAL_COSU];
  try solve [rewrite !data_at_rec_eq; try (simple_if_tac; auto);
  try solve [rewrite default_val_eq, unfold_fold_reptype; apply mapsto_mapsto_]].
  + rewrite !data_at_rec_eq.
    apply array_pred_ext_derives.
    {
      intros; rewrite default_val_eq.
      rewrite unfold_fold_reptype.
      rewrite Zlength_correct in H1.
      rewrite <- Z2Nat_max0.
      rewrite Zlength_list_repeat by omega.
      omega.
    }
    rewrite default_val_eq. simpl.
    intros.
    rewrite !at_offset_eq3.
    rewrite default_val_eq with (t0 := (Tarray t z a)), unfold_fold_reptype.
    eapply derives_trans.
    apply IH; auto.
    - pose_size_mult cenv_cs t (0 :: i :: i + 1 :: Z.max 0 z :: nil); simpl in H; try omega.
    - eapply align_compatible_rec_Tarray_inv; eauto.
      apply range_max0; auto.
    - apply derives_refl'. f_equal. unfold Znth. rewrite if_false by omega.
      rewrite nth_list_repeat'; auto.
      apply Nat2Z.inj_lt. rewrite Z2Nat.id, Z2Nat_id' by omega. omega.
  + rewrite !data_at_rec_eq.
    rewrite default_val_eq, unfold_fold_reptype.
    assert (members_no_replicate (co_members (get_co id)) = true) as NO_REPLI
      by apply get_co_members_no_replicate.
    apply struct_pred_ext_derives; [auto |].
    intros.
    rewrite !withspacer_spacer.
    simpl @fst.
    apply sepcon_derives; [auto |].
    rewrite !at_offset_eq3.
    rewrite Forall_forall in IH.
    specialize (IH (i, (field_type i (co_members (get_co id))))).
    spec IH; [apply in_members_field_type; auto |].
    unfold snd in IH.
    unfold struct_default_val.
    unfold proj_struct.
    rewrite compact_prod_proj_gen by (apply in_members_field_type; auto).
    apply IH; try unfold fst.
    - apply complete_legal_cosu_type_field_type; auto.
    - pose_field; omega.
    - eapply align_compatible_rec_Tstruct_inv'; eauto.
  + assert (co_members (get_co id) = nil \/ co_members (get_co id) <> nil)
      by (destruct (co_members (get_co id)); [left | right]; congruence).
    destruct H1.
    - rewrite !data_at_rec_eq.
      generalize (unfold_reptype v) (unfold_reptype (default_val (Tunion id a))); rewrite H1; intros.
      apply derives_refl.
    - rewrite data_at_rec_eq.
      rewrite memory_block_data_at_rec_default_val by auto.
      eapply derives_trans.
      * assert (members_no_replicate (co_members (get_co id)) = true) as NO_REPLI
          by apply get_co_members_no_replicate.
        apply union_pred_ext_derives with
          (P1 := fun _ _ => memory_block sh (sizeof (Tunion id a)));
          [auto | reflexivity | ].
        intros.
        clear H3.
        pose proof @compact_sum_inj_in _ _ (co_members (get_co id)) (unfold_reptype v) _ _ H2.
        apply in_map with (f := fst) in H3; unfold fst in H3.
        rewrite withspacer_spacer, sizeof_Tunion.
        simpl.
        pattern (co_sizeof (get_co id)) at 2;
        replace (co_sizeof (get_co id)) with (sizeof (field_type i (co_members (get_co id))) +
          (co_sizeof (get_co id) - sizeof (field_type i (co_members (get_co id))))) by omega.
        rewrite sepcon_comm.
        rewrite memory_block_split by (pose_field; omega).
        apply sepcon_derives; [| rewrite spacer_memory_block by (simpl; auto);
                                 unfold offset_val; solve_mod_modulus; auto ].
        rewrite <- memory_block_data_at_rec_default_val; auto.
        { 
          rewrite Forall_forall in IH.
          specialize (IH (i, (field_type i (co_members (get_co id))))).
          spec IH; [apply in_members_field_type; auto |].
          unfold snd in IH.
          apply IH.
          + apply complete_legal_cosu_type_field_type; auto.
          + pose_field; omega.
          + eapply align_compatible_rec_Tunion_inv'; eauto.
        } {
          apply complete_legal_cosu_type_field_type; auto.
        } {
          pose_field; omega.
        } {
          eapply align_compatible_rec_Tunion_inv'; eauto.
        }
        apply derives_refl.
      * rewrite sizeof_Tunion.
        rewrite memory_block_union_pred by (apply get_co_members_nil_sizeof_0).
        auto.
Qed.

Definition value_fits: forall t, reptype t -> Prop :=
  type_func (fun t => reptype t -> Prop)
    (fun t v =>
       if type_is_volatile t then True else tc_val' t (repinject t v))
    (fun t n a P v => Zlength (unfold_reptype v) =  Z.max 0 n /\ Forall P (unfold_reptype v))
    (fun id a P v => struct_value_fits_aux (co_members (get_co id)) (co_members (get_co id)) P (unfold_reptype v))
    (fun id a P v => union_value_fits_aux (co_members (get_co id)) (co_members (get_co id)) P (unfold_reptype v)).

Lemma value_fits_eq:
  forall t v,
  value_fits t v =
  match t as t0 return (reptype t0 -> Prop)  with
  | Tarray t' n a => fun v0 : reptype (Tarray t' n a) =>
    (fun v1 : list (reptype t') =>
     Zlength v1 = Z.max 0 n /\ Forall (value_fits t') v1)
      (unfold_reptype v0)
| Tstruct i a =>
    fun v0 : reptype (Tstruct i a) =>
     struct_Prop (co_members (get_co i))
       (fun it : ident * type =>
        value_fits (field_type (fst it) (co_members (get_co i)))) (unfold_reptype v0)
| Tunion i a =>
    fun v0 : reptype (Tunion i a) =>
     union_Prop (co_members (get_co i))
       (fun it : ident * type =>
        value_fits (field_type (fst it) (co_members (get_co i)))) (unfold_reptype v0)
  | t0 => fun v0: reptype t0 =>
             (if type_is_volatile t0
              then True
              else tc_val' t0 (repinject t0 v0))
  end v.
Proof.
intros.
unfold value_fits.
rewrite type_func_eq.
destruct t; auto.
apply struct_value_fits_aux_spec.
apply union_value_fits_aux_spec.
Qed.

Lemma value_fits_type_changable: forall (t1 t2: type) v1 v2,
  t1 = t2 ->
  JMeq v1 v2 ->
  value_fits t1 v1 = value_fits t2 v2.
Proof.
  intros.
  subst t2.
  apply JMeq_eq in H0.
  rewrite H0.
  reflexivity.
Qed.

Lemma default_value_fits:
  forall t, value_fits t (default_val t).
Proof.
  intros.
  type_induction t; try destruct f; rewrite value_fits_eq;
  try solve [simpl; try (simple_if_tac; auto); apply tc_val'_Vundef];
  rewrite default_val_eq, unfold_fold_reptype.
  + (* Tarray *)
    split.
    - rewrite Zlength_list_repeat', Z2Nat_id'; auto.
    - apply Forall_list_repeat; auto.
  + (* Tstruct *)
    cbv zeta in IH.
    apply struct_Prop_compact_prod_gen.
    - apply get_co_members_no_replicate.
    - rewrite Forall_forall in IH.
      intros; apply IH.
      apply in_members_field_type; auto.
  + (* Tunion *)
    cbv zeta in IH.
    apply union_Prop_compact_sum_gen.
    - apply get_co_members_no_replicate.
    - rewrite Forall_forall in IH.
      intros; apply IH.
      apply in_members_field_type; auto.
Qed.

Lemma data_at_rec_value_fits: forall sh t v p,
  data_at_rec sh t v p |-- !! value_fits t v.
Proof.
  intros until p.
  revert v p; type_induction t; intros;
  rewrite value_fits_eq, data_at_rec_eq;
  try solve [normalize];
  try solve [cbv zeta; simple_if_tac; [normalize | apply mapsto_tc_val']].
  + (* Tarray *)
    eapply derives_trans; [apply array_pred_local_facts |].
    - intros.
      unfold at_offset.
      instantiate (1 := fun x => value_fits t x); simpl.
      apply IH.
    - apply prop_derives.
      intros [? ?]; split; auto.
      rewrite Zlength_correct in *.
      omega.
  + (* Tstruct *)
    apply struct_pred_local_facts; [apply get_co_members_no_replicate |].
    intros.
    rewrite withspacer_spacer.
    unfold at_offset.
    cbv zeta in IH.
    rewrite Forall_forall in IH.
    specialize (IH (i, (field_type i (co_members (get_co id))))).
    spec IH; [apply in_members_field_type; auto |].
    eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply IH] |].
    rewrite sepcon_comm; apply derives_left_sepcon_right_corable; auto.
  + (* Tunion *)
    apply union_pred_local_facts; [apply get_co_members_no_replicate |].
    intros.
    rewrite withspacer_spacer.
    unfold at_offset.
    cbv zeta in IH.
    rewrite Forall_forall in IH.
    specialize (IH (i, (field_type i (co_members (get_co id))))).
    spec IH; [apply in_members_field_type; auto |].
    eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply IH] |].
    rewrite sepcon_comm; apply derives_left_sepcon_right_corable; auto.
Qed.

Lemma data_at_rec_share_join:
  forall sh1 sh2 sh t v b ofs,
    sepalg.join sh1 sh2 sh ->
   data_at_rec sh1 t v (Vptr b ofs) * data_at_rec sh2 t v (Vptr b ofs) = data_at_rec sh t v (Vptr b ofs).
Proof.
  intros.
  revert v ofs; pattern t; type_induction t; intros;
  rewrite !data_at_rec_eq;
    try solve [simple_if_tac;
        [ apply memory_block_share_join; auto
        | apply mapsto_share_join; auto]];
    try solve [normalize].
  + (* Tarray *)
    rewrite array_pred_sepcon.
    apply array_pred_ext; auto.
    intros.
    unfold at_offset; simpl.
    apply IH.
  + (* Tstruct *)
    rewrite struct_pred_sepcon.
    apply struct_pred_ext; [apply get_co_members_no_replicate |].
    intros.
Opaque field_type field_offset.
    simpl.
Transparent field_type field_offset.
    rewrite !withspacer_spacer.
    rewrite !spacer_memory_block by (simpl; auto).
    rewrite !sepcon_assoc, (sepcon_comm (at_offset _ _ _)), <- !sepcon_assoc.
    erewrite memory_block_share_join by eassumption.
    rewrite sepcon_assoc; f_equal.
    unfold at_offset.
    cbv zeta in IH.
    rewrite Forall_forall in IH.
    pose proof H0.
    apply in_members_field_type in H0.
    rewrite sepcon_comm.
    etransitivity; [apply (IH (i, field_type i (co_members (get_co id))) H0) |].
    f_equal.
    apply JMeq_eq.
    apply (@proj_compact_prod_JMeq _ _ _ (fun it => reptype (field_type (fst it) (co_members (get_co id)))) (fun it => reptype (field_type (fst it) (co_members (get_co id))))); auto.
  + rewrite union_pred_sepcon.
    apply union_pred_ext; [apply get_co_members_no_replicate | reflexivity | ].
    intros.
Opaque field_type field_offset.
    simpl.
Transparent field_type field_offset.
    rewrite !withspacer_spacer.
    rewrite !spacer_memory_block by (simpl; auto).
    rewrite !sepcon_assoc, (sepcon_comm (data_at_rec _ _ _ _)), <- !sepcon_assoc.
    erewrite memory_block_share_join by eassumption.
    rewrite sepcon_assoc; f_equal.
    unfold at_offset.
    cbv zeta in IH.
    rewrite Forall_forall in IH.
    apply compact_sum_inj_in in H1.
    rewrite sepcon_comm.
    etransitivity; [apply (IH (i, field_type i (co_members (get_co id))) H1) |].
    f_equal.
    apply JMeq_eq.
    apply (@proj_compact_sum_JMeq _ _ _ (fun it => reptype (field_type (fst it) (co_members (get_co id)))) (fun it => reptype (field_type (fst it) (co_members (get_co id))))); auto.
Qed.

Lemma nonreadable_memory_block_data_at_rec:
  forall sh t v b ofs
  (LEGAL_COSU: complete_legal_cosu_type t = true),
  0 <= ofs /\ ofs + sizeof t < Ptrofs.modulus ->
  align_compatible_rec cenv_cs t ofs ->
  ~ readable_share sh ->
  value_fits t v ->
  memory_block sh (sizeof t) (Vptr b (Ptrofs.repr ofs)) = data_at_rec sh t v (Vptr b (Ptrofs.repr ofs)).
Proof.
  intros.
  symmetry.
  revert v ofs LEGAL_COSU H H0 H1 H2;
  pattern t; type_induction t; (* try destruct i; try destruct s; *) intros;
    try inversion LEGAL_COSU;
    rewrite value_fits_eq in H2; cbv beta zeta in H2;
    try match type of H2 with
        | context [type_is_volatile ?t] =>
            destruct (type_is_volatile t) eqn:?;
             [apply by_value_data_at_rec_volatile | apply by_value_data_at_rec_nonreachable2]; auto
        end;
    rewrite !data_at_rec_eq.
  + simpl in H, H0.
    rewrite array_pred_ext with
     (P1 := fun i _ p => memory_block sh (sizeof t)
                          (offset_val (sizeof t * i) p))
     (v1 := list_repeat (Z.to_nat (Z.max 0 z)) (default_val t)); auto.
    rewrite memory_block_array_pred; auto.
    - apply Z.le_max_l.
    - rewrite (proj1 H2).
      symmetry; apply Zlength_list_repeat; auto.
      apply Z.le_max_l.
    - intros.
      rewrite at_offset_eq3.
      unfold offset_val; solve_mod_modulus.
      unfold Znth. rewrite if_false by omega.
      rewrite Z.sub_0_r.
      assert (value_fits t (nth (Z.to_nat i) (unfold_reptype v) (default_val t))).
      {
        destruct H2.
        rewrite Forall_forall in H5.
        apply H5.
        apply nth_In.
        apply Nat2Z.inj_lt.
        rewrite <- Zlength_correct, H2, Z2Nat.id by omega.
        omega.
      }
      apply IH; auto.
      * pose_size_mult cenv_cs t (0 :: i :: i + 1 :: Z.max 0 z :: nil); omega.
      * eapply align_compatible_rec_Tarray_inv; eauto.
        apply range_max0; auto.
  + rewrite struct_pred_ext with
     (P1 := fun it _ p =>
              memory_block sh
               (field_offset_next cenv_cs (fst it) (co_members (get_co id)) (co_sizeof (get_co id)) -
                  field_offset cenv_cs (fst it) (co_members (get_co id)))
               (offset_val (field_offset cenv_cs (fst it) (co_members (get_co id))) p))
     (v1 := (struct_default_val (co_members (get_co id))));
    [| apply get_co_members_no_replicate |].
    - rewrite memory_block_struct_pred.
      * rewrite sizeof_Tstruct; auto.
      * apply get_co_members_nil_sizeof_0.
      * apply get_co_members_no_replicate.
      * rewrite sizeof_Tstruct in H.
        pose proof co_consistent_sizeof cenv_cs (get_co id) (get_co_consistent id).
        erewrite complete_legal_cosu_type_Tstruct in H3 by exact LEGAL_COSU.
        unfold sizeof_composite in H3.
        revert H3; pose_align_le; intros; omega.
      * rewrite sizeof_Tstruct in H.
        auto.
    - intros.
      pose proof get_co_members_no_replicate id as NO_REPLI.
      rewrite withspacer_spacer.
      simpl @fst.
      rewrite spacer_memory_block by (simpl; auto).
      rewrite at_offset_eq3.
      unfold offset_val; solve_mod_modulus.
      unfold struct_default_val.
      rewrite Forall_forall in IH.
      specialize (IH (i, field_type i (co_members (get_co id)))).
      spec IH; [apply in_members_field_type; auto |].
      unfold snd in IH.
      apply struct_Prop_proj with (i := i) (d:= d0) in H2; auto.
      rewrite IH; auto.
      * rewrite Z.add_assoc, sepcon_comm, <- memory_block_split by (pose_field; omega).
        f_equal; omega.
      * apply complete_legal_cosu_type_field_type; auto.
      * simpl fst. pose_field; omega.
      * eapply align_compatible_rec_Tstruct_inv'; eauto.
  + assert (co_members (get_co id) = nil \/ co_members (get_co id) <> nil)
      by (clear; destruct (co_members (get_co id)); [left | right]; congruence).
    destruct H3.
    - rewrite sizeof_Tunion.
      rewrite (get_co_members_nil_sizeof_0 _ H3).
      forget (unfold_reptype v) as v'; simpl in v'.
      generalize (unfold_reptype (default_val (Tunion id a)));
      clear H2; revert v'; rewrite H3 in *;
      intros.
      simpl.
      rewrite memory_block_zero.
      normalize.
    - rewrite union_pred_ext with
       (P1 := fun it _ => memory_block sh (co_sizeof (get_co id)))
       (v1 := (unfold_reptype v));
      [| apply get_co_members_no_replicate | reflexivity |].
      * rewrite memory_block_union_pred by (apply get_co_members_nil_sizeof_0).
        rewrite sizeof_Tunion.
        auto.
      * intros.
        pose proof get_co_members_no_replicate id as NO_REPLI.
        pose proof @compact_sum_inj_in _ _ (co_members (get_co id)) _ _ _ H6.
        apply in_map with (f := fst) in H7; unfold fst in H7.
        rewrite withspacer_spacer.
        simpl @fst.
        rewrite spacer_memory_block by (simpl; auto).
        unfold offset_val; solve_mod_modulus.
        rewrite Forall_forall in IH.
        specialize (IH (i, field_type i (co_members (get_co id)))).
        spec IH; [apply in_members_field_type; auto |].
        unfold snd in IH.
        apply union_Prop_proj with (i := i) (d := d0) in H2; auto.
        rewrite IH; auto.
        { rewrite sepcon_comm, <- memory_block_split by (pose_field; omega).
          f_equal; f_equal; omega.
        } {
          apply complete_legal_cosu_type_field_type; auto.
        } {
          simpl fst; pose_field; omega.
        } {
          eapply align_compatible_rec_Tunion_inv'; eauto.
        }
Qed.

(*
Lemma f_equal_Int_repr:
  forall i j, i=j -> Int.repr i = Int.repr j.
Proof. intros; congruence. Qed.

Lemma sizeof_Tarray:
  forall t (n:Z) a, n >= 0 ->
      sizeof (Tarray t n a) = (sizeof t * n)%Z.
Proof.
intros; simpl. rewrite Z.max_r; omega.
Qed.

Lemma data_at_Tarray_ext_derives: forall sh t n a v v',
  (forall i, 0 <= i < n ->
     data_at sh t (Znth i v (default_val _)) |-- data_at sh t (Znth i v' (default_val _))) ->
  data_at sh (Tarray t n a) v |-- data_at sh (Tarray t n a) v'.
Proof.
  intros.
  unfold data_at.
  simpl; intro p.
  unfold array_at'.
  normalize.
  apply rangespec_ext_derives.
  intros.
  rewrite !Z.add_0_l.
  rewrite !Z.sub_0_r.
  assert (legal_alignas_type t = true).
  {
    unfold legal_alignas_type in H2.
    simpl in H2.
    rewrite andb_true_iff in H2.
    tauto.
  }
  assert (alignof t | sizeof t * i).
  {
    apply Z.divide_mul_l.
    apply legal_alignas_sizeof_alignof_compat, H5.
  }
  rewrite !data_at_rec_at_offset with (pos := (sizeof t * i)%Z) by auto.
  rewrite !at_offset_eq by (rewrite <- data_at_rec_offset_zero; reflexivity).
  assert (legal_nested_field (Tarray t n a) (ArraySubsc i :: nil)) by solve_legal_nested_field.
  pose proof size_compatible_nested_field _ (ArraySubsc i :: nil) _ H7 H0.
  unfold nested_field_type2, nested_field_offset2 in H8; simpl in H8.
  pose proof align_compatible_nested_field _ (ArraySubsc i :: nil) _ H7 H2 H1.
  unfold nested_field_type2, nested_field_offset2 in H9; simpl in H9.
  simpl in H8, H9.
  specialize (H i H4 (offset_val (Int.repr (sizeof t * i)) p)).
  unfold data_at in H.
  simpl in H.
  normalize in H.
Qed.

Lemma data_at_Tarray_ext: forall sh t n a v v',
  (forall i, 0 <= i < n ->
    data_at sh t (Znth i v (default_val _)) =
      data_at sh t (Znth i v' (default_val _))) ->
  data_at sh (Tarray t n a) v = data_at sh (Tarray t n a) v'.
Proof.
  intros.
  apply pred_ext; apply data_at_Tarray_ext_derives; auto;
  intros; rewrite H by auto; auto.
Qed.

*)

End CENV.

Lemma data_at_rec_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall (sh: Share.t) (t: type) v1 v2,
  JMeq v1 v2 ->
  cs_preserve_type cs_from cs_to (coeq _ _) t = true ->
  @data_at_rec cs_from sh t v1 = @data_at_rec cs_to sh t v2.
Proof.
  intros sh t.
  type_induction t; intros.
  + rewrite !data_at_rec_eq; auto.
  + rewrite !data_at_rec_eq.
    change val in v1, v2.
    apply JMeq_eq in H.
    subst; auto.
  + rewrite !data_at_rec_eq.
    change val in v1, v2.
    apply JMeq_eq in H.
    subst; auto.
  + rewrite !data_at_rec_eq.
    change val in v1, v2.
    apply JMeq_eq in H.
    subst; auto.
  + rewrite !data_at_rec_eq.
    change val in v1, v2.
    apply JMeq_eq in H.
    subst; auto.
  + (* Tarray *)
    rewrite !data_at_rec_eq.
    extensionality p.
    assert (JMeq (unfold_reptype v1) (unfold_reptype v2)).
    {
      eapply JMeq_trans; [| eapply JMeq_trans; [exact H |]].
      + apply (unfold_reptype_JMeq (Tarray t z a) v1).
      + apply JMeq_sym, (unfold_reptype_JMeq (Tarray t z a) v2).
    }
    apply array_pred_ext.
    - apply list_func_JMeq; [apply reptype_change_composite; auto | auto].
    - intros.
      rewrite (IH (Znth (i - 0) (unfold_reptype v1)) (Znth (i - 0) (unfold_reptype v2))); auto.
      * f_equal.
        f_equal.
        apply sizeof_change_composite; auto.
      *
        pose (Znthx (A: Type) (i: Z) (al: list A) (d: A) := @Znth A d i al).
        change  (@Znth (@reptype cs_from t) (@Inhabitant_reptype cs_from t) (i - 0)
                                     (@unfold_reptype cs_from (Tarray t z a) v1))
       with (Znthx (@reptype cs_from t) (i-0) (@unfold_reptype cs_from (Tarray t z a) v1)(@Inhabitant_reptype cs_from t)).
        change  (@Znth (@reptype cs_to t) (@Inhabitant_reptype cs_to t) (i - 0)
                                     (@unfold_reptype cs_to (Tarray t z a) v2))
       with (Znthx (@reptype cs_to t) (i-0) (@unfold_reptype cs_to (Tarray t z a) v2)(@Inhabitant_reptype cs_to t)).
       change (@Znthx (@reptype cs_from t) (i - 0)) 
     with ((fun X: Type => @Znthx X (i - 0)) (@reptype cs_from t)).
        change (@Znthx (@reptype cs_to t) (i - 0)) 
          with ((fun X: Type => @Znthx X (i - 0)) (@reptype cs_to t)).
      apply @list_func_JMeq'; auto.
      apply default_val_change_composite; auto.
  + rewrite !data_at_rec_eq.
    auto.
  + (* Tstruct *)
    rewrite !data_at_rec_eq.
    extensionality p.
    assert (JMeq (unfold_reptype v1) (unfold_reptype v2)).
    {
      eapply JMeq_trans; [| eapply JMeq_trans; [exact H |]].
      + apply (unfold_reptype_JMeq (Tstruct _ _) v1).
      + apply JMeq_sym, (unfold_reptype_JMeq (Tstruct _ _) v2).
    }
    revert H1; clear H.
    forget (unfold_reptype v1) as v1'.
    forget (unfold_reptype v2) as v2'.
    clear v1 v2.
    intros.
    simpl in v1', v2', H1.
    unfold reptype_structlist in *.
    revert v1' H1.
    rewrite co_members_get_co_change_composite in * by auto.
    intros.
    pose proof (fun i => field_offset_change_composite _ i H0) as HH0.
    pose proof (fun i => field_offset_next_change_composite _ i H0) as HH1.
    apply members_spec_change_composite in H0.
    apply struct_pred_ext; [apply get_co_members_no_replicate |].
    intros.
    f_equal; [f_equal | | f_equal ]; auto.
    - apply sizeof_change_composite; auto.
      rewrite Forall_forall in H0.
      apply H0.
      apply in_members_field_type.
      auto.
    - clear HH0 HH1.
      simpl fst in *.
      revert d0 d1 v1' v2' IH H0 H1.
      generalize (co_members (get_co id)) at 1 2 3 5 7 8 9 10 11 12 13 15 17 19 21 23 24 26; intros.
      pose proof in_members_field_type _ _ H.
      rewrite Forall_forall in IH, H0.
      specialize (IH _ H2); pose proof (H0 _ H2).
      apply IH; auto.
      apply (@proj_struct_JMeq i (co_members (@get_co cs_to id)) (fun it : ident * type => @reptype cs_from (field_type (@fst ident type it) m)) (fun it : ident * type => @reptype cs_to (field_type (@fst ident type it) m))); auto.
      * intros. 
        rewrite reptype_change_composite; [reflexivity |].
        apply H0.
        apply in_members_field_type; auto.
      * apply get_co_members_no_replicate.
  + (* Tunion *)
    rewrite !data_at_rec_eq.
    extensionality p.
    assert (JMeq (unfold_reptype v1) (unfold_reptype v2)).
    {
      eapply JMeq_trans; [| eapply JMeq_trans; [exact H |]].
      + apply (unfold_reptype_JMeq (Tunion _ _) v1).
      + apply JMeq_sym, (unfold_reptype_JMeq (Tunion _ _) v2).
    }
    revert H1; clear H.
    forget (unfold_reptype v1) as v1'.
    forget (unfold_reptype v2) as v2'.
    clear v1 v2.
    intros.
    simpl in v1', v2', H1.
    unfold reptype_structlist in *.
    revert v1' H1.
    rewrite co_members_get_co_change_composite in * by auto.
    intros.
    pose proof (fun i => field_offset_change_composite _ i H0) as HH0.
    pose proof (fun i => field_offset_next_change_composite _ i H0) as HH1.
    pose proof H0 as H0'.
    apply members_spec_change_composite in H0.
    apply union_pred_ext.
    { apply get_co_members_no_replicate. }
    {
      apply members_union_inj_JMeq; auto.
      2: apply get_co_members_no_replicate.
      intros.
      rewrite reptype_change_composite; [reflexivity |].
      apply in_members_field_type in H.
      rewrite Forall_forall in H0.
      apply (H0 _ H).
    }
    intros.
    f_equal.
    - apply sizeof_change_composite; auto.
      rewrite Forall_forall in H0.
      apply H0.
      apply in_members_field_type.
      apply compact_sum_inj_in in H.
      apply (in_map fst) in H.
      auto.
    - apply co_sizeof_get_co_change_composite.
      auto.
    - clear HH0 HH1.
      simpl fst in *.
      revert d0 d1 v1' v2' IH H0 H1 H H2.
      unfold reptype_unionlist.
      generalize (co_members (get_co id)) at 1 2 3 5 7 8 9 10 11 12 13 15 17 19 22 25 27 29 30 32; intros.
      apply compact_sum_inj_in in H2.
      apply (in_map fst) in H2.
      apply in_members_field_type in H2.
      rewrite Forall_forall in IH, H0.
      specialize (IH _ H2); pose proof (H0 _ H2).
      apply IH; auto.
      apply (@proj_union_JMeq i (co_members (@get_co cs_to id)) (fun it : ident * type => @reptype cs_from (field_type (@fst ident type it) m)) (fun it : ident * type => @reptype cs_to (field_type (@fst ident type it) m))); auto.
      * intros.
        rewrite reptype_change_composite; [reflexivity |].
        apply H0.
        apply in_members_field_type; auto.
      * apply get_co_members_no_replicate.
Qed.

(**** tactics for value_fits  ****)

Lemma value_fits_Tstruct:
  forall {cs: compspecs} t (v: reptype t) i a m v2 r,
  t = Tstruct i a ->
  m = co_members (get_co i)  ->
  JMeq (@unfold_reptype cs t v) v2 ->
  r =struct_Prop m
          (fun it => value_fits (field_type (fst it) m))  v2 ->
  value_fits t v = r.
Proof.
intros.
subst.
rewrite value_fits_eq; simpl.
f_equal.
apply JMeq_eq in H1. auto.
Qed.

Lemma value_fits_Tunion:
  forall {cs: compspecs} t (v: reptype t) i a m v2 r,
  t = Tunion i a ->
  m = co_members (get_co i)  ->
  JMeq (@unfold_reptype cs t v) v2 ->
  r =union_Prop m
          (fun it => value_fits (field_type (fst it) m))  v2 ->
  value_fits t v = r.
Proof.
intros.
subst.
rewrite value_fits_eq; simpl.
f_equal.
apply JMeq_eq in H1. auto.
Qed.

Lemma value_fits_by_value_defined:
  forall {cs: compspecs} t t' v r,
   type_is_by_value t = true ->
   repinject t v <> Vundef  ->
   t = t' ->
   (r = if type_is_volatile t' then True
       else tc_val t' (repinject t v)) ->
   value_fits t v = r.
Proof.
intros. subst t' r.
rewrite value_fits_eq.
unfold tc_val'.
destruct t; inv H;
 (simple_if_tac; auto; apply prop_ext; intuition).
Qed.

Lemma value_fits_by_value_Vundef:
  forall {cs: compspecs} t v,
   type_is_by_value t = true ->
   repinject t v = Vundef  ->
   value_fits t v = True.
Proof.
intros.
rewrite value_fits_eq.
unfold tc_val'.
destruct t; inv H;
 (simple_if_tac; auto; auto; apply prop_ext; intuition).
Qed.

Lemma value_fits_by_value:
  forall {cs: compspecs} t t' v r,
   type_is_by_value t = true ->
   t = t' ->
   (r = if type_is_volatile t then True
       else tc_val' t' (repinject t v)) ->
   value_fits t v = r.
Proof.
intros. subst r t'.
rewrite value_fits_eq.
unfold tc_val'.
destruct t; inv H;
 (simple_if_tac; auto; apply prop_ext; intuition).
Qed.

Lemma value_fits_Tarray:
  forall {cs: compspecs} t (v: reptype t) t' n a
    (v' : list (reptype t')) r,
  t = (Tarray t' n a) ->
  JMeq (unfold_reptype v) v' ->
  n >= 0 ->
  r = (Zlength v' = n /\ Forall (value_fits t') v') ->
  value_fits t v =r.
Proof.
intros.
subst. rewrite value_fits_eq.
apply JMeq_eq in H0. rewrite H0.
rewrite Z.max_r by omega. auto.
Qed.

Ltac cleanup_unfold_reptype :=
    match goal with |- JMeq (unfold_reptype ?A) _ =>
                 instantiate (1:=A); apply JMeq_refl
    end.

Ltac simplify_value_fits' :=
first
 [erewrite value_fits_Tstruct;
    [ | reflexivity
    | simpl; reflexivity
    | cleanup_unfold_reptype
    | simpl; reflexivity]
 |erewrite value_fits_Tarray;
    [ | reflexivity
    | cleanup_unfold_reptype
    | repeat subst_any; try computable; omega
    | simpl; reflexivity
    ]
 | erewrite value_fits_by_value_defined;
   [ | reflexivity
   | repeat subst_any; clear; simpl; intro; discriminate
   | simpl; lazy beta iota zeta delta [field_type]; simpl; reflexivity
   | simpl; reflexivity
   ]
 | rewrite value_fits_by_value_Vundef;
   [ | reflexivity | reflexivity
   ]
 | erewrite value_fits_by_value;
   [ | reflexivity
   | simpl; lazy beta iota zeta delta [field_type]; simpl; reflexivity
   | simpl; reflexivity
   ]
 ];
 cbv beta;
 repeat match goal with |- context [@reptype ?cs ?t] =>
   change (@reptype cs t) with val
 end.

Tactic Notation "simplify_value_fits" :=
  simplify_value_fits'.

Tactic Notation "simplify_value_fits" "in" hyp(H) :=
  match type of H with ?A =>
  let a := fresh "a" in set (a:=A) in H;
   let H1 := fresh in assert (H1: a = A) by (apply eq_refl);
   clearbody a;
   match goal with |- ?B =>
    let BB := fresh "BB" in set (BB:=B);
   revert H1; simplify_value_fits'; intro H1; subst a; subst BB
  end
 end.

Tactic Notation "simplify_value_fits" "in" "*" :=
repeat match goal with
 | H: context [value_fits _ _ _] |- _ =>
  simplify_value_fits in H
end;
 repeat simplify_value_fits'.

(*** end tactics for value_fits ***)