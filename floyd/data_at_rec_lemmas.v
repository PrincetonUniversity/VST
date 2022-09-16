Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.type_induction.
Require Import VST.floyd.nested_pred_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require VST.floyd.aggregate_pred. Import VST.floyd.aggregate_pred.aggregate_pred.
Import VST.floyd.aggregate_pred.auxiliary_pred.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.jmeq_lemmas.
Require Import VST.zlist.sublist.
Require Export VST.floyd.fieldlist.
Require Export VST.floyd.aggregate_type.
Import compcert.lib.Maps.

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
                        (field_offset cenv_cs (name_member it) (co_members (get_co id)) + sizeof (field_type (name_member it) (co_members (get_co id))))
                        (field_offset_next cenv_cs (name_member it) (co_members (get_co id)) (co_sizeof (get_co id)))
                        (at_offset (data_at_rec (field_type (name_member it) (co_members (get_co id))) v) (field_offset cenv_cs (name_member it) (co_members (get_co id)))))
  | Tunion id a => union_pred (co_members (get_co id))
                     (fun it v => withspacer sh
                      (sizeof (field_type (name_member it) (co_members (get_co id))))
                      (co_sizeof (get_co id))
                      (data_at_rec (field_type (name_member it) (co_members (get_co id))) v))
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

Lemma zero_val_Tint: forall i s a, zero_val (Tint i s a) = Vint Int.zero.
Proof.
intros.
 unfold zero_val, zero_val', reptype_gen0; simpl;
    unfold eq_rect_r; rewrite <- eq_rect_eq; auto.
Qed.
   
Lemma zero_val_Tlong: forall s a, zero_val (Tlong s a) = Vlong Int64.zero.
Proof.
intros.
 unfold zero_val, zero_val', reptype_gen0; simpl;
    unfold eq_rect_r; rewrite <- eq_rect_eq; auto.
Qed.
   
Lemma zero_val_Tpointer: forall t a, zero_val (Tpointer t a) = nullval. 
Proof.
intros.
 unfold zero_val, zero_val', reptype_gen0; simpl;
    unfold eq_rect_r; rewrite <- eq_rect_eq; auto.
Qed.

Lemma zero_val_Tfloat32: forall a, zero_val (Tfloat F32 a) = Vsingle Float32.zero.
Proof.
intros.
 unfold zero_val, zero_val', reptype_gen0; simpl;
    unfold eq_rect_r; rewrite <- eq_rect_eq; auto.
Qed.


Lemma zero_val_Tfloat64: forall a, zero_val (Tfloat F64 a) = Vfloat Float.zero.
Proof.
intros.
 unfold zero_val, zero_val', reptype_gen0; simpl;
    unfold eq_rect_r; rewrite <- eq_rect_eq; auto.
Qed.

Ltac unknown_big_endian_hack :=
  (* This is necessary on machines where Archi.big_endian is a Parameter 
    rather than a Definition.  When Archi.big_endian is a constant true or false,
   then it's much easier. *)
 match goal with H1: (align_chunk _ | _) |- _ |-- res_predicates.address_mapsto ?ch ?v ?sh (?b, Ptrofs.unsigned ?i) =>
   constructor;
   replace v with (decode_val ch (repeat (Byte Byte.zero) (Z.to_nat (size_chunk ch))));
   [ apply (mapsto_memory_block.address_mapsto_zeros'_address_mapsto sh ch b i H1) | ];
    unfold decode_val, decode_int, rev_if_be;
     destruct Archi.big_endian;
     reflexivity
 end.

Lemma by_value_data_at_rec_zero_val: forall sh t p,
  type_is_by_value t = true ->
  size_compatible t p ->
  align_compatible t p ->
  type_is_volatile t = false ->
  mapsto_zeros (sizeof t) sh p |-- data_at_rec sh t (zero_val t) p.
Proof.
  intros.
  rewrite data_at_rec_eq.
  pose proof (sizeof_pos t).
  destruct t; try destruct f; try solve [inversion H]; rewrite H2;
  destruct p; try apply FF_left;
  unfold mapsto_zeros; apply derives_extract_prop; intros [? ?];
  rewrite mapsto_memory_block.address_mapsto_zeros_eq;
  rewrite Z2Nat.id by lia;
  unfold mapsto; rewrite H2.
- rewrite zero_val_Tint.
   change (unfold_reptype ?A) with A.
    destruct i,s; simpl;
    (eapply align_compatible_rec_by_value_inv in H1; [ | reflexivity]);
   rewrite prop_true_andp by (clear; compute; repeat split; try congruence; auto);
   rewrite (prop_true_andp (_ /\ _)) 
    by (split; auto; intros _; compute; repeat split; try congruence; auto);
   (if_tac; [apply orp_right1 | ]).
   all: try (constructor; apply mapsto_memory_block.address_mapsto_zeros'_nonlock_permission_bytes).
   all: try unknown_big_endian_hack.
- rewrite zero_val_Tlong.
   change (unfold_reptype ?A) with A.
    destruct s; simpl;
    (eapply align_compatible_rec_by_value_inv in H1; [ | reflexivity]);
   rewrite prop_true_andp by (clear; compute; repeat split; try congruence; auto);
   rewrite (prop_true_andp (_ /\ _)) 
    by (split; auto; intros _; compute; repeat split; try congruence; auto);
   (if_tac; [apply orp_right1 | ]).
   all: try (constructor; apply mapsto_memory_block.address_mapsto_zeros'_nonlock_permission_bytes; computable).
   all: try unknown_big_endian_hack.
- rewrite zero_val_Tfloat32;
   change (unfold_reptype ?A) with A.
    (eapply align_compatible_rec_by_value_inv in H1; [ | reflexivity]).
   simpl. rewrite prop_true_andp by auto.
   rewrite (prop_true_andp (_ /\ _)) 
    by (split; auto; intros _; compute; repeat split; try congruence; auto);
   (if_tac; [apply orp_right1 | ]); constructor.
   all: try apply mapsto_memory_block.address_mapsto_zeros'_nonlock_permission_bytes.
   all: try apply (mapsto_memory_block.address_mapsto_zeros'_address_mapsto sh _ _ _ H1).
- rewrite zero_val_Tfloat64;
   change (unfold_reptype ?A) with A.
    (eapply align_compatible_rec_by_value_inv in H1; [ | reflexivity]).
   simpl. rewrite prop_true_andp by auto.
   rewrite (prop_true_andp (_ /\ _)) 
    by (split; auto; intros _; compute; repeat split; try congruence; auto);
   (if_tac; [apply orp_right1 | ]).
   all: try (constructor; apply mapsto_memory_block.address_mapsto_zeros'_nonlock_permission_bytes).
   all: try unknown_big_endian_hack.
- rewrite zero_val_Tpointer.
   change (unfold_reptype ?A) with A.
    (eapply align_compatible_rec_by_value_inv in H1; [ | reflexivity]).
   simpl access_mode; cbv beta iota.
  rewrite prop_true_andp by apply mapsto_memory_block.tc_val_pointer_nullval'.
   rewrite (prop_true_andp (_ /\ _))
      by (split; auto; intro; apply mapsto_memory_block.tc_val_pointer_nullval'). 
   (if_tac; [apply orp_right1 | ]).
   all: try (constructor; apply mapsto_memory_block.address_mapsto_zeros'_nonlock_permission_bytes).
   all: try unknown_big_endian_hack.
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
    lia.
  + unfold align_compatible.
    solve_mod_modulus.
    pose proof sizeof_pos t.
    rewrite Zmod_small by lia.
    auto.
Qed.

Lemma by_value_data_at_rec_zero_val2: forall sh t b ofs,
  type_is_by_value t = true ->
  0 <= ofs /\ ofs + sizeof t < Ptrofs.modulus ->
  align_compatible_rec cenv_cs t ofs ->
  type_is_volatile t = false ->
  mapsto_zeros (sizeof t) sh (Vptr b (Ptrofs.repr ofs)) |-- 
  data_at_rec sh t (zero_val t) (Vptr b (Ptrofs.repr ofs)).
Proof.
  intros.
  apply by_value_data_at_rec_zero_val; auto.
  + unfold size_compatible.
    solve_mod_modulus.
    pose_mod_le ofs.
    lia.
  + unfold align_compatible.
    solve_mod_modulus.
    pose proof sizeof_pos t.
    rewrite Zmod_small by lia.
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
    lia.
  + unfold align_compatible.
    solve_mod_modulus.
    pose proof sizeof_pos t.
    rewrite Zmod_small by lia.
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
  rewrite Z.add_mod by lia.
  rewrite Z.mod_mod by lia.
  rewrite <- Z.add_mod by lia.
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
    { intros. lia. }
  pose proof Int.modulus_pos.
  pose proof Int.unsigned_range i.
  apply Z.mod_le; lia.
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
    rewrite Z.mod_small by lia.
    apply Z.divide_add_r; assumption.
  + pose proof sizeof_pos cenv_cs t.
    assert (Int.unsigned i + pos = Int.modulus) by lia.
    rewrite H4.
    rewrite Z_mod_same_full.
    apply Z.divide_0_r.
Qed.
*)
Lemma Znth_nil: forall {A}{d: Inhabitant A} n, Znth n (@nil A) = default.
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

Lemma nth_repeat: forall A i n (x :A),
    nth i (repeat x n) x = x.
Proof.
 induction i; destruct n; simpl; auto.
Qed.

Lemma nth_repeat': forall A i n (x y :A),
    (i < n)%nat ->
    nth i (repeat x n) y = x.
Proof.
 induction i; destruct n; simpl; intros; auto.
 lia. lia.
 apply IHi; auto. lia.
Qed.

 Lemma Z2Nat_max0: forall z, Z.to_nat (Z.max 0 z) = Z.to_nat z.
 Proof.
  intros.
  rewrite Z.max_comm, <- Z_to_nat_max, Nat2Z.id.
  auto.
Qed.

Lemma range_max0: forall x z, 0 <= x < Z.max 0 z <-> 0 <= x < z.
Proof.
  intros.
  destruct (zlt z 0).
  + rewrite Z.max_l by lia.
    lia.
  + rewrite Z.max_r by lia.
    lia.
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
     (v1 := Zrepeat (default_val t) (Z.max 0 z));
     auto.
    rewrite memory_block_array_pred; auto.
    - apply Z.le_max_l.
    - f_equal. unfold Zrepeat.
      f_equal.  lia.
    - intros.
      rewrite at_offset_eq3.
      unfold offset_val; solve_mod_modulus.
      unfold Znth, Zrepeat. rewrite if_false by lia.
      rewrite nth_repeat.
      unfold expr.sizeof,  Ctypes.sizeof in H; fold @Ctypes.sizeof in H; fold (sizeof t) in H.
      pose_size_mult cs t (0 :: i :: i + 1 :: Z.max 0 z :: nil).
      assert (sizeof t = 0 -> sizeof t * i = 0)%Z by (intros HH; rewrite HH, Z.mul_0_l; auto).
      apply IH; auto; try lia.
      eapply align_compatible_rec_Tarray_inv; [eassumption |].
      apply range_max0; auto.
  + rewrite default_val_eq.
    rewrite unfold_fold_reptype.
    rewrite struct_pred_ext with
     (P1 := fun it _ p =>
              memory_block sh
               (field_offset_next cenv_cs (name_member it) (co_members (get_co id)) (co_sizeof (get_co id)) -
                  field_offset cenv_cs (name_member it) (co_members (get_co id)))
               (offset_val (field_offset cenv_cs (name_member it) (co_members (get_co id))) p))
     (v1 := (struct_default_val (co_members (get_co id))));
    [| apply get_co_members_no_replicate |].
    - change (sizeof ?A) with (expr.sizeof A) in *.
       rewrite memory_block_struct_pred.
      * rewrite sizeof_Tstruct; auto.
      * apply get_co_members_nil_sizeof_0.
      * eapply complete_Tstruct_plain; eauto.
      * apply get_co_members_no_replicate.
      * rewrite sizeof_Tstruct in H.
        pose proof co_consistent_sizeof cenv_cs (get_co id) (get_co_consistent id).
        erewrite complete_legal_cosu_type_Tstruct in H1 by eauto.
        pose proof co_consistent_sizeof cenv_cs (get_co id) (get_co_consistent id).
        unfold sizeof_composite in H1.
        assert (PLAIN := complete_Tstruct_plain _ _ LEGAL_COSU).
        rewrite <- plain_members_sizeof_struct in H1 by auto.
        revert H1; pose_align_le. intros; lia.
      * rewrite sizeof_Tstruct in H.
        lia.
    - intros.
      pose proof get_co_members_no_replicate id as NO_REPLI.
      rewrite withspacer_spacer.
      simpl @fst.
      rewrite spacer_memory_block by (simpl; auto).
      rewrite at_offset_eq3.
      unfold offset_val; solve_mod_modulus.
      unfold struct_default_val.
      unfold proj_struct.
      rewrite compact_prod_proj_gen by (apply in_get_member; auto).
      rewrite Forall_forall in IH.
      specialize (IH (get_member i (co_members (get_co id)))).
      rewrite name_member_get in *.
      spec IH; [apply in_get_member; auto |].
      rewrite IH; clear IH.
      * rewrite Z.add_assoc, sepcon_comm.
         rewrite <- memory_block_split by (auto; pose_field; lia).
        f_equal; lia.
      * apply complete_legal_cosu_type_field_type.
         eapply complete_Tstruct_plain; eauto.
        auto.
      * simpl fst. pose_field; lia.
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
        apply in_map with (f := name_member) in H4; unfold fst in H4.
        rewrite withspacer_spacer.
        simpl @fst.
        rewrite spacer_memory_block by (simpl; auto).
        unfold offset_val; solve_mod_modulus.
        unfold union_default_val.
        unfold proj_union.
        unfold members_union_inj in *.
        rewrite compact_sum_proj_gen; [| auto].
        rewrite Forall_forall in IH.
        specialize (IH (get_member i (co_members (get_co id)))).
        rewrite name_member_get in *.
        spec IH; [apply in_get_member; auto |].
        rewrite IH.
        { 
          rewrite sepcon_comm, <- memory_block_split by (pose_field; lia).
          f_equal; f_equal; lia.
        } {
          apply complete_legal_cosu_type_field_type.
         eapply complete_Tunion_plain; eauto.
          auto.
        } {
          pose_field; lia.
        } {
          simpl fst. eapply align_compatible_rec_Tunion_inv'; eauto.
        }
Qed.

Fixpoint fully_nonvolatile {cs: compspecs} (rank: nat) (t: type) : bool :=
 match rank with
 | O => negb (type_is_volatile t) 
 | S r => negb (type_is_volatile t) &&
               match t with
               | Tarray t' _ _ => fully_nonvolatile r t'
               | Tstruct id _ => match cenv_cs ! id with 
                                          | Some co => forallb (fully_nonvolatile r) (map type_member (co_members co))
                                          | None => false
                                          end
               | Tunion id _ => match cenv_cs ! id with 
                                          | Some co => forallb (fully_nonvolatile r) (map type_member (co_members co))
                                          | None => false
                                          end
               | _ => true
               end
 end.

Lemma fully_nonvolatile_stable:
  forall {cs: compspecs} r r' t, (r >= r')%nat -> fully_nonvolatile r t = true -> fully_nonvolatile r' t = true.
Proof.
induction r; destruct r'; simpl; intros; auto.
inv H.
rewrite andb_true_iff in H0; destruct H0; auto.
rewrite andb_true_iff in H0|-*; destruct H0; split; auto.
destruct t; auto.
apply IHr; auto; lia.
all: destruct (cenv_cs ! i); auto;
rewrite forallb_forall in H1|-*; intros; apply H1 in H2; apply IHr; auto; lia.
Qed.

(* We use (Vptr b (Int.repr ofs)) instead of p because size_compatible is more  *)
(* difficult to use than simple arithmetic in induction proof.                  *)
Lemma mapsto_zeros_data_at_rec_zero_val: forall sh
  (Hsh: readable_share sh)
  t b ofs
  (LEGAL_COSU: complete_legal_cosu_type t = true),
  0 <= ofs /\ ofs + sizeof t < Ptrofs.modulus ->
  align_compatible_rec cenv_cs t ofs ->
  fully_nonvolatile (rank_type cenv_cs t) t = true ->
  mapsto_zeros (sizeof t) sh (Vptr b (Ptrofs.repr ofs)) |--
    data_at_rec sh t (zero_val t) (Vptr b (Ptrofs.repr ofs)).
Proof.
  intros sh ? t.
  type_induction t; intros;
  try solve [inversion LEGAL_COSU];
    try (replace (rank_type _ _) with O in H1
         by (try destruct i; try destruct s; try destruct f; reflexivity);
    apply negb_true_iff in H1);
  try (apply by_value_data_at_rec_zero_val2; [reflexivity | assumption.. ]);
  rename H1 into Hvol;
  rewrite data_at_rec_eq.
 + rewrite (zero_val_eq (Tarray t z a)).
     rewrite unfold_fold_reptype.
    eapply derives_trans; [ | 
    apply array_pred_ext_derives with
     (P0 := fun i _ p => mapsto_zeros (sizeof t) sh
                          (offset_val (sizeof t * i) p))
     (v0 := Zrepeat (zero_val t) (Z.max 0 z))];
     auto.
    apply mapsto_zeros_array_pred; auto.
    - apply Z.le_max_l.
    - unfold Zrepeat. 
      rewrite Z2Nat_max0; auto.
    - intros.
      change (unfold_reptype ?A) with A.
      rewrite at_offset_eq3.
      unfold offset_val; solve_mod_modulus.
      unfold Znth, Zrepeat. rewrite if_false by lia.
      rewrite nth_repeat' by lia.
      unfold expr.sizeof,  Ctypes.sizeof in H; fold @Ctypes.sizeof in H; fold (sizeof t) in H.
      pose_size_mult cs t (0 :: i :: i + 1 :: Z.max 0 z :: nil).
      assert (sizeof t = 0 -> sizeof t * i = 0)%Z by (intros HH; rewrite HH, Z.mul_0_l; auto).
      apply IH; auto; try lia.
      eapply align_compatible_rec_Tarray_inv; [eassumption |].
      apply range_max0; auto.
  + rewrite zero_val_eq.
     rewrite unfold_fold_reptype.
    eapply derives_trans; [ |
    apply struct_pred_ext_derives with
     (P0 := fun it _ p =>
              mapsto_zeros
               (field_offset_next cenv_cs (name_member it) (co_members (get_co id)) (co_sizeof (get_co id)) -
                  field_offset cenv_cs (name_member it) (co_members (get_co id))) sh
               (offset_val (field_offset cenv_cs (name_member it) (co_members (get_co id))) p))
     (v0 := (struct_zero_val (co_members (get_co id))))];
    [| apply get_co_members_no_replicate |].
    - change (sizeof ?A) with (expr.sizeof A) in *.
       eapply derives_trans; [apply mapsto_zeros_struct_pred with (m := co_members (get_co id)) | ];
         rewrite ?sizeof_Tstruct; auto.
      * apply get_co_members_nil_sizeof_0.
      * eapply complete_Tstruct_plain; eauto.
      * apply get_co_members_no_replicate.
      * rewrite sizeof_Tstruct in H. 
        pose proof co_consistent_sizeof cenv_cs (get_co id) (get_co_consistent id).
        erewrite complete_legal_cosu_type_Tstruct in H1 by eauto.
        pose proof co_consistent_sizeof cenv_cs (get_co id) (get_co_consistent id).
        unfold sizeof_composite in H1.
        revert H1; pose_align_le; intros.
        rewrite plain_members_sizeof_struct in *
           by (eapply complete_Tstruct_plain; eauto).
        lia.
      * rewrite sizeof_Tstruct in H.
        lia.
      * apply derives_refl.
    - intros.
      pose proof get_co_members_no_replicate id as NO_REPLI.
      rewrite withspacer_spacer.
      simpl @fst.
      rewrite spacer_memory_block by (simpl; auto).
      rewrite at_offset_eq3.
      unfold offset_val; solve_mod_modulus.
      unfold struct_zero_val.
      unfold proj_struct.
      rewrite compact_prod_proj_gen by (apply in_get_member; auto).
      rewrite Forall_forall in IH.
      specialize (IH (get_member i (co_members (get_co id)))).
      rewrite name_member_get in *.
      spec IH; [apply in_get_member; auto |].
      eapply derives_trans; [ | apply sepcon_derives; [apply derives_refl | apply IH]]; clear IH.
      *
      eapply derives_trans; [ | apply sepcon_derives; [apply mapsto_zeros_memory_block; auto | apply derives_refl ]].
      simpl fst. 
       rewrite Z.add_assoc. rewrite sepcon_comm.
       rewrite <- aggregate_pred.mapsto_zeros_split by (pose_field; lia).
       apply derives_refl'; f_equal; lia.
      * apply complete_legal_cosu_type_field_type.
         eapply complete_Tstruct_plain; eauto.
        auto.
      * pose_field; lia.
      * eapply align_compatible_rec_Tstruct_inv'; eauto.
      * clear - LEGAL_COSU Hvol.
         unfold get_co. simpl in *.
         destruct (cenv_cs ! id) eqn:?H; try discriminate.
         simpl in Hvol. rewrite H in Hvol.
         destruct (Ctypes.field_type i (co_members c)) eqn:?H; auto.
         destruct (co_su c); try discriminate.
         assert (In (Member_plain i t) (co_members c)). {
             clear - LEGAL_COSU H0. induction (co_members c) as [|[??|]]; simpl; [ | | discriminate]. 
             inv H0. simpl in H0. if_tac in H0. subst. inv H0; auto. right; auto.
         }
         rewrite forallb_forall in Hvol. specialize (Hvol  _ (in_map type_member _ _ H1)).
         pose proof (cenv_legal_su _ _ H). apply (complete_legal_cosu_member _ i t) in H2; auto.
         eapply fully_nonvolatile_stable; try eassumption.
         rewrite (co_consistent_rank cenv_cs c (cenv_consistent _ _ H)).        
         apply (rank_type_members cenv_cs (Member_plain i t) (co_members c)); auto.
  + assert (co_members (get_co id) = nil \/ co_members (get_co id) <> nil)
      by (destruct (co_members (get_co id)); [left | right]; congruence).
    destruct H1.
    - rewrite sizeof_Tunion.
      rewrite (get_co_members_nil_sizeof_0 _ H1).
      generalize (unfold_reptype (zero_val (Tunion id a)));
      rewrite H1 in *;
      intros.
      simpl.
      normalize. apply derives_refl.
    - rewrite zero_val_eq.
      rewrite unfold_fold_reptype.
      eapply derives_trans; [ | apply union_pred_ext_derives with
       (P0 := fun it _ => mapsto_zeros(co_sizeof (get_co id)) sh)
       (v0 := (union_zero_val (co_members (get_co id))))];
      [| apply get_co_members_no_replicate | reflexivity |].
      * rewrite sizeof_Tunion.
         apply mapsto_zeros_union_pred. (apply get_co_members_nil_sizeof_0).
      * intros.
        pose proof get_co_members_no_replicate id as NO_REPLI.
        pose proof @compact_sum_inj_in _ _ (co_members (get_co id)) (union_zero_val (co_members (get_co id))) _ _ H3.
        apply in_map with (f := name_member) in H4; unfold fst in H4.
        rewrite withspacer_spacer.
        simpl @fst.
        rewrite spacer_memory_block by (simpl; auto).
        unfold offset_val; solve_mod_modulus.
        unfold union_zero_val.
        unfold proj_union.
        unfold members_union_inj in *.
        rewrite compact_sum_proj_gen; [| auto].
        rewrite Forall_forall in IH.
        specialize (IH (get_member i (co_members (get_co id)))).
      rewrite name_member_get in *.
      spec IH; [apply in_get_member; auto |].
        eapply derives_trans; [ | apply sepcon_derives; [ apply derives_refl | apply IH]]; clear IH.
        -- rewrite sepcon_comm. simpl fst.
             eapply derives_trans; [ | apply sepcon_derives; [apply derives_refl | apply mapsto_zeros_memory_block; auto ]].
            rewrite <- aggregate_pred.mapsto_zeros_split by (pose_field; lia).
          apply derives_refl'.
          f_equal; f_equal; lia.
       --
          apply complete_legal_cosu_type_field_type.
          eapply complete_Tunion_plain; eauto.
          auto.
        --
          pose_field; lia.
        --
           eapply align_compatible_rec_Tunion_inv'; eauto.
       --clear - LEGAL_COSU Hvol.
         unfold get_co. simpl in *.
         destruct (cenv_cs ! id) eqn:?H; try discriminate.
         destruct (co_su c); try discriminate.
         simpl in Hvol. rewrite H in Hvol.
         destruct (Ctypes.field_type i (co_members c)) eqn:?H; auto.
         assert (In (Member_plain i t) (co_members c)). {
             clear - LEGAL_COSU H0. induction (co_members c) as [|[??|]]; simpl; [ | | discriminate]. 
             inv H0. simpl in H0. if_tac in H0. subst. inv H0; auto. right; auto.
         }
         rewrite forallb_forall in Hvol. specialize (Hvol  _ (in_map type_member _ _ H1)).
         pose proof (cenv_legal_su _ _ H). apply (complete_legal_cosu_member _ i t) in H2; auto.
         eapply fully_nonvolatile_stable; try eassumption.
         rewrite (co_consistent_rank cenv_cs c (cenv_consistent _ _ H)).        
         apply (rank_type_members cenv_cs (Member_plain i t) (co_members c)); auto.
Qed.

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
      unfold Zrepeat.
      rewrite <- Z2Nat_max0.
      rewrite Zlength_repeat by lia.
      lia.
    }
    rewrite default_val_eq. simpl.
    intros.
    rewrite !at_offset_eq3.
    rewrite @default_val_eq with (t := (Tarray t z a)), unfold_fold_reptype.
    eapply derives_trans.
    apply IH; auto.
    - pose_size_mult cs t (0 :: i :: i + 1 :: Z.max 0 z :: nil).
       unfold sizeof in H; simpl in H; fold (sizeof t) in H; lia.
    - eapply align_compatible_rec_Tarray_inv; eauto.
      apply range_max0; auto.
    - apply derives_refl'. f_equal. unfold Znth, Zrepeat. rewrite if_false by lia.
      rewrite nth_repeat'; auto.
      apply Nat2Z.inj_lt. rewrite Z2Nat.id, Z2Nat_id' by lia. lia.
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
    specialize (IH (get_member i (co_members (get_co id)))).
    spec IH; [apply in_get_member; auto |].
    unfold struct_default_val.
    unfold proj_struct.
    rewrite compact_prod_proj_gen by (apply in_get_member; auto).
    apply IH; rewrite name_member_get.
    - apply complete_legal_cosu_type_field_type; auto.
       eapply complete_Tstruct_plain; eauto.
    - pose_field; lia.
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
        apply in_map with (f := name_member) in H3; rewrite name_member_get in H3.
        change (sizeof ?A) with (expr.sizeof A).
        rewrite withspacer_spacer, sizeof_Tunion.
       set (i' := name_member (get_member i (co_members (get_co id)))) in *.
        pattern (co_sizeof (get_co id)) at 2;
        replace (co_sizeof (get_co id)) with (sizeof (field_type i' (co_members (get_co id))) +
          (co_sizeof (get_co id) - sizeof (field_type i' (co_members (get_co id))))) by lia.
        rewrite sepcon_comm.
        rewrite memory_block_split by (subst i'; rewrite name_member_get; pose_field; lia).
        apply sepcon_derives; [| rewrite spacer_memory_block by (simpl; auto);
                                 unfold offset_val; solve_mod_modulus; auto ].

        rewrite <- memory_block_data_at_rec_default_val; auto.
        { 
          rewrite Forall_forall in IH.
          specialize (IH (get_member i (co_members (get_co id)))).
          spec IH; [apply in_get_member; auto |].
          apply IH.
          + apply complete_legal_cosu_type_field_type; auto.
              eapply complete_Tunion_plain; eauto.
              rewrite name_member_get; auto.
          + rewrite name_member_get; pose_field; lia.
          + rewrite name_member_get;  eapply align_compatible_rec_Tunion_inv'; eauto.
        } {
          apply complete_legal_cosu_type_field_type; auto.
          eapply complete_Tunion_plain; eauto.
          subst i'; rewrite name_member_get; auto.    
        } {
          subst i'; rewrite name_member_get.
          pose_field; lia.
        } {
          eapply align_compatible_rec_Tunion_inv'; eauto.
          subst i'; rewrite name_member_get; auto.    
        }
      * 
        rewrite sizeof_Tunion.
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
       (fun it : member =>
        value_fits (field_type (name_member it) (co_members (get_co i)))) (unfold_reptype v0)
| Tunion i a =>
    fun v0 : reptype (Tunion i a) =>
     union_Prop (co_members (get_co i))
       (fun it : member =>
        value_fits (field_type (name_member it) (co_members (get_co i)))) (unfold_reptype v0)
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
    - unfold Zrepeat; rewrite Zlength_repeat', Z2Nat_id'; auto.
    - apply Forall_repeat; auto.
  + (* Tstruct *)
    cbv zeta in IH.
    apply struct_Prop_compact_prod_gen.
    - apply get_co_members_no_replicate.
    - rewrite Forall_forall in IH.
      intros; apply IH.
      apply in_get_member; auto.
  + (* Tunion *)
    cbv zeta in IH.
    apply union_Prop_compact_sum_gen.
    - apply get_co_members_no_replicate.
    - rewrite Forall_forall in IH.
      intros; apply IH.
      apply in_get_member; auto.
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
      lia.
  + (* Tstruct *)
    apply struct_pred_local_facts; [apply get_co_members_no_replicate |].
    intros.
    rewrite withspacer_spacer.
    unfold at_offset.
    cbv zeta in IH.
    rewrite Forall_forall in IH.
    specialize (IH (get_member i (co_members (get_co id)))).
    spec IH; [apply in_get_member; auto |].
    eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply IH] |].
    rewrite sepcon_comm; apply derives_left_sepcon_right_corable; auto.
  + (* Tunion *)
    apply union_pred_local_facts; [apply get_co_members_no_replicate |].
    intros.
    rewrite withspacer_spacer.
    unfold at_offset.
    cbv zeta in IH.
    rewrite Forall_forall in IH.
    specialize (IH (get_member i (co_members (get_co id)))).
    spec IH; [apply in_get_member; auto |].
    eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply IH] |].
    rewrite sepcon_comm; apply derives_left_sepcon_right_corable; auto.
Qed. 

Lemma mapsto_values_cohere:
  forall sh1 sh2 t (R:type_is_by_value t = true) b ofs,
    type_is_volatile t = false ->
    readable_share sh1 -> readable_share sh2 -> 
  forall (v1 v2:val) (V1: ~ JMeq v1 Vundef) (V2: ~ JMeq v2 Vundef),
    mapsto sh1 t (Vptr b ofs) v1 * mapsto sh2 t (Vptr b ofs) v2 |-- !!(v1=v2).
Proof.
intros; destruct t; try discriminate R; unfold mapsto; simpl; simpl in *.
 + destruct i; destruct s; simpl; rewrite ! if_true by trivial; rewrite H.
    - eapply derives_trans.
      { apply sepcon_derives.
        + apply orp_left; [ apply derives_refl |].
          apply andp_left1. apply prop_left. intros; subst. elim V1. apply JMeq_refl.
        + apply orp_left; [ apply derives_refl |].
          apply andp_left1. apply prop_left. intros; subst. elim V2. apply JMeq_refl. }
      normalize. rewrite derives_eq.
      apply res_predicates.address_mapsto_value_cohere.
    - eapply derives_trans.
      { apply sepcon_derives.
        + apply orp_left; [ apply derives_refl |].
          apply andp_left1. apply prop_left. intros; subst. elim V1. apply JMeq_refl.
        + apply orp_left; [ apply derives_refl |].
          apply andp_left1. apply prop_left. intros; subst. elim V2. apply JMeq_refl. }
      normalize. rewrite derives_eq.
      apply res_predicates.address_mapsto_value_cohere.
    - eapply derives_trans.
      { apply sepcon_derives.
        + apply orp_left; [ apply derives_refl |].
          apply andp_left1. apply prop_left. intros; subst. elim V1. apply JMeq_refl.
        + apply orp_left; [ apply derives_refl |].
          apply andp_left1. apply prop_left. intros; subst. elim V2. apply JMeq_refl. }
      normalize. rewrite derives_eq.
      apply res_predicates.address_mapsto_value_cohere.
    - eapply derives_trans.
      { apply sepcon_derives.
        + apply orp_left; [ apply derives_refl |].
          apply andp_left1. apply prop_left. intros; subst. elim V1. apply JMeq_refl.
        + apply orp_left; [ apply derives_refl |].
          apply andp_left1. apply prop_left. intros; subst. elim V2. apply JMeq_refl. }
      normalize. rewrite derives_eq.
      apply res_predicates.address_mapsto_value_cohere.
    - eapply derives_trans.
      { apply sepcon_derives.
        + apply orp_left; [ apply derives_refl |].
          apply andp_left1. apply prop_left. intros; subst. elim V1. apply JMeq_refl.
        + apply orp_left; [ apply derives_refl |].
          apply andp_left1. apply prop_left. intros; subst. elim V2. apply JMeq_refl. }
      normalize. rewrite derives_eq.
      apply res_predicates.address_mapsto_value_cohere.
    - eapply derives_trans.
      { apply sepcon_derives.
        + apply orp_left; [ apply derives_refl |].
          apply andp_left1. apply prop_left. intros; subst. elim V1. apply JMeq_refl.
        + apply orp_left; [ apply derives_refl |].
          apply andp_left1. apply prop_left. intros; subst. elim V2. apply JMeq_refl. }
      normalize. rewrite derives_eq.
      apply res_predicates.address_mapsto_value_cohere.
    - eapply derives_trans.
      { apply sepcon_derives.
        + apply orp_left; [ apply derives_refl |].
          apply andp_left1. apply prop_left. intros; subst. elim V1. apply JMeq_refl.
        + apply orp_left; [ apply derives_refl |].
          apply andp_left1. apply prop_left. intros; subst. elim V2. apply JMeq_refl. }
      normalize. rewrite derives_eq.
      apply res_predicates.address_mapsto_value_cohere.
    - eapply derives_trans.
      { apply sepcon_derives.
        + apply orp_left; [ apply derives_refl |].
          apply andp_left1. apply prop_left. intros; subst. elim V1. apply JMeq_refl.
        + apply orp_left; [ apply derives_refl |].
          apply andp_left1. apply prop_left. intros; subst. elim V2. apply JMeq_refl. }
      normalize. rewrite derives_eq.
      apply res_predicates.address_mapsto_value_cohere.
  + rewrite H; clear R. rewrite ! if_true by trivial.
    - eapply derives_trans.
      { apply sepcon_derives.
        + apply orp_left; [ apply derives_refl |].
          apply andp_left1. apply prop_left. intros; subst. elim V1. apply JMeq_refl.
        + apply orp_left; [ apply derives_refl |].
          apply andp_left1. apply prop_left. intros; subst. elim V2. apply JMeq_refl. }
      normalize. rewrite derives_eq.
      apply res_predicates.address_mapsto_value_cohere.
  + rewrite H; clear R. destruct f; rewrite ! if_true by trivial.
    - eapply derives_trans.
      { apply sepcon_derives.
        + apply orp_left; [ apply derives_refl |].
          apply andp_left1. apply prop_left. intros; subst. elim V1. apply JMeq_refl.
        + apply orp_left; [ apply derives_refl |].
          apply andp_left1. apply prop_left. intros; subst. elim V2. apply JMeq_refl. }
      normalize. rewrite derives_eq.
      apply res_predicates.address_mapsto_value_cohere.
    - eapply derives_trans.
      { apply sepcon_derives.
        + apply orp_left; [ apply derives_refl |].
          apply andp_left1. apply prop_left. intros; subst. elim V1. apply JMeq_refl.
        + apply orp_left; [ apply derives_refl |].
          apply andp_left1. apply prop_left. intros; subst. elim V2. apply JMeq_refl. }
      normalize. rewrite derives_eq.
      apply res_predicates.address_mapsto_value_cohere.
  + rewrite H; clear R. rewrite ! if_true by trivial.
    - eapply derives_trans.
      { apply sepcon_derives.
        + apply orp_left; [ apply derives_refl |].
          apply andp_left1. apply prop_left. intros; subst. elim V1. apply JMeq_refl.
        + apply orp_left; [ apply derives_refl |].
          apply andp_left1. apply prop_left. intros; subst. elim V2. apply JMeq_refl. }
      normalize. rewrite derives_eq.
      apply res_predicates.address_mapsto_value_cohere.
Qed.

Definition value_defined_byvalue t v :=
if type_is_volatile t then False else tc_val t (repinject t v).

Definition value_defined : forall t, reptype t -> Prop :=
  type_func (fun t => reptype t -> Prop)
    value_defined_byvalue
    (fun t n a P v => Zlength (unfold_reptype v) =  Z.max 0 n /\ Forall P (unfold_reptype v))
    (fun id a P v => struct_value_fits_aux (co_members (get_co id)) (co_members (get_co id)) P (unfold_reptype v))
    (fun id a P v => False). (* don't permit unions, for now ; otherwise: 
                 union_value_fits_aux (co_members (get_co id)) (co_members (get_co id)) P (unfold_reptype v))
*)

Lemma value_defined_eq:
  forall t v,
  value_defined t v =
  match t as t0 return (reptype t0 -> Prop)  with
  | Tarray t' n a => fun v0 : reptype (Tarray t' n a) =>
    (fun v1 : list (reptype t') =>
     Zlength v1 = Z.max 0 n /\ Forall (value_defined t') v1)
      (unfold_reptype v0)
| Tstruct i a =>
    fun v0 : reptype (Tstruct i a) =>
     struct_Prop (co_members (get_co i))
       (fun it : member =>
        value_defined (field_type (name_member it) (co_members (get_co i)))) (unfold_reptype v0)
| Tunion i a =>
    fun v0 : reptype (Tunion i a) =>
     False (*
     union_Prop (co_members (get_co i))
       (fun it : member =>
        value_defined (field_type (name_member it) (co_members (get_co i)))) (unfold_reptype v0)
      *)
  | t0 => value_defined_byvalue t0
  end v.
Proof.
intros.
unfold value_defined.
rewrite type_func_eq.
destruct t; auto.
apply struct_value_fits_aux_spec.
(* apply union_value_fits_aux_spec. *)
Qed.

Lemma value_defined_not_volatile:
  forall t v, value_defined t v -> type_is_volatile t = false.
Proof.
intros.
destruct t; try reflexivity; 
do 5 red in H;
destruct (type_is_volatile _); auto; contradiction.
Qed.

Local Definition field_atx sh m (sz: Z) (it : member)
                   (v : reptype
                           (field_type (name_member it) m))
       := 
                 withspacer sh
                   (field_offset (@cenv_cs cs) (name_member it) m
                      + sizeof
                          (field_type (name_member it) m))
                   (field_offset_next (@cenv_cs cs) (name_member it) m sz)
                   (at_offset
                      (data_at_rec sh
                         (field_type (name_member it) m) v)
                      (field_offset cenv_cs (name_member it) m)).

Local Definition field_cohere sh1 sh2 
  m b it :=
 forall (v1 v2: reptype (field_type (name_member it) m)) ofs,
        type_is_volatile
          (field_type (name_member it) m) = false ->
        value_defined
          (field_type (name_member it) m) v1 ->
        value_defined
          (field_type (name_member it) m) v2 ->
        data_at_rec sh1
          (field_type (name_member it) m) v1
          (Vptr b ofs)
          * data_at_rec sh2
              (field_type (name_member it) m) v2
              (Vptr b ofs) |-- !! (v1 = v2).

Lemma data_at_rec_values_cohere:
       forall (sh1 sh2 : share) (t : type),
       forall (b : block) (ofs : ptrofs),
       readable_share sh1 ->
       readable_share sh2 ->
       forall v1 v2 : reptype t,
       value_defined t v1 ->
       value_defined t v2 ->
       data_at_rec sh1 t v1 (Vptr b ofs)
         * data_at_rec sh2 t v2 (Vptr b ofs) 
        |-- !! (v1 = v2).
Proof.
  intros *. pose proof I. intros.
  clear H. pose proof (value_defined_not_volatile _ _ H2).
  red in H2, H3.
  revert v1 v2 ofs H H2 H3.
  pattern t; type_induction t; intros;
  rewrite !data_at_rec_eq; try solve [ normalize];
try solve [
  do 4 red in H2, H3;
  rewrite ?H in *;
 try (
   apply (mapsto_values_cohere sh1 sh2); trivial;
  try destruct f;
   (intro H5; apply JMeq_eq in H5; subst; try contradiction));
  try (hnf in H2; destruct (eqb_type _ _) in H2; contradiction);
  try (hnf in H3; destruct (eqb_type _ _) in H3; contradiction)].
- (* array *)
destruct H2.
change (Forall (value_defined t) (unfold_reptype v1)) in H4.
destruct H3.
change (Forall (value_defined t) (unfold_reptype v2)) in H5.
unfold array_pred.
destruct (zle z 0).
rewrite Z.max_l in * by lia.
apply prop_right.
rewrite Zlength_length in H2,H3 by lia.
destruct v1; inv H2. destruct v2; inv H3. auto.
rewrite Z.max_r in * by lia.
clear H.
pose proof (Z2Nat.id z) ltac:(lia).
set (n := Z.to_nat z) in *.
clearbody n.
rewrite <- H in *.
subst z.
change (@unfold_reptype cs (Tarray t (Z.of_nat n) a) v1) with v1 in *.
change (@unfold_reptype cs (Tarray t (Z.of_nat n) a) v2) with v2 in *.
assert (type_is_volatile t = false). {
 clear - H2 H4 g.
 destruct v1. rewrite Zlength_nil in H2. lia.
 inv H4.
 apply value_defined_not_volatile in H1; auto.
}
clear g.
change (list (reptype t)) in v1,v2.
revert v1 v2 H5 H3 H4 H2; induction n; intros.
apply prop_right.
clear - H3 H2.
rewrite Zlength_length in H2,H3 by lia.
destruct v1; inv H2. destruct v2; inv H3. auto.
rewrite inj_S in *.
rewrite !(split_array_pred 0 (Z.of_nat n) (Z.succ (Z.of_nat n))) by lia.
rewrite !Z.sub_0_r.
rewrite !(sublist_one (Z.of_nat n)) by lia.
unfold Z.succ.
rewrite !array_pred_len_1.
match goal with |- (?a*?b)*(?c*?d) |-- _ =>
    apply derives_trans with ((a*c)*(b*d)); [ cancel | ] end.
apply derives_trans 
  with (!! (sublist 0 (Z.of_nat n) v1 = sublist 0 (Z.of_nat n) v2) 
           * !! (Znth (Z.of_nat n) v1 = Znth (Z.of_nat n) v2)).
apply sepcon_derives.
apply IHn.
apply Forall_sublist; auto.
Zlength_solve.
apply Forall_sublist; auto.
Zlength_solve.
unfold at_offset.
apply IH; auto.
apply Forall_Znth; auto; lia.
apply Forall_Znth; auto; lia.
rewrite sepcon_prop_prop.
apply prop_derives; intros [? ?].
replace v1 with (sublist 0 (Z.of_nat n) v1 ++ (Znth (Z.of_nat n) v1 :: nil)).
replace v2 with (sublist 0 (Z.of_nat n) v2 ++ (Znth (Z.of_nat n) v2 :: nil)).
rewrite H6,H7; auto.
clear - H3.
rewrite <- sublist_last_1 by lia.
apply sublist_same; lia.
clear - H2.
rewrite <- sublist_last_1 by lia.
apply sublist_same; lia.
-
cbv zeta in IH.
clear H.
change (type_func _ _ _ _ _ ) with value_defined in *.
unfold aggregate_pred.struct_pred.
rewrite value_defined_eq in H2, H3.
cbv zeta in IH.
fold (field_atx sh1 (co_members (get_co id)) (co_sizeof (get_co id))).
fold (field_atx sh2 (co_members (get_co id)) (co_sizeof (get_co id))).
fold (field_cohere sh1 sh2 (co_members (get_co id)) b) in IH.
eapply derives_trans with (!! (unfold_reptype v1 = unfold_reptype v2)).
2:{  clear. 
       apply prop_derives; intro.
       unfold reptype, unfold_reptype in *.
       unfold eq_rect in *.
        destruct (reptype_eq (Tstruct id a)).
         auto.
}
set (u1 := unfold_reptype v1) in *.
set (u2 := unfold_reptype v2) in *.
clearbody u1. clearbody u2.
simpl in u1,u2. clear v1 v2.
destruct (get_co id); simpl in *.
rename co_sizeof into sz.
rename co_alignof into al.
rename co_rank into rank.
rename co_members into m.
unfold reptype_structlist in u1,u2.
assert (
forall sh1 sh2 b m0 m
 (IH : Forall (field_cohere sh1 sh2 m0 b) m)
 (ofs : ptrofs)
 (u1 u2 : compact_prod
       (map (fun it : member => reptype (field_type (name_member it) m0))
          m))
 (H2 : struct_Prop m
       (fun it : member =>
        value_defined
          match Ctypes.field_type (name_member it) m0 with
          | Errors.OK t => t
          | Errors.Error _ => Tvoid
          end) u1)
 (H3 : struct_Prop m
       (fun it : member =>
        value_defined
          match Ctypes.field_type (name_member it) m0 with
          | Errors.OK t => t
          | Errors.Error _ => Tvoid
          end) u2),
struct_pred m (field_atx sh1 m0 sz) u1 (Vptr b ofs)
  * struct_pred m (field_atx sh2 m0 sz) u2 (Vptr b ofs) |-- !! (u1 = u2)).
2: eauto.
clear.
intros.
destruct m as [ | a0 m].
apply prop_right; destruct u1,u2; auto.
revert a0 IH u1 u2 H2 H3.
induction m as [ | a1 m]; intros.
+
simpl.
inv IH. clear H4.
red in H1.
unfold field_atx.
rewrite !withspacer_spacer.
rewrite !spacer_memory_block by (simpl; auto).
set (x1 := memory_block sh1 _ _).
set (x2 := memory_block sh2 _ _).
clearbody x1 x2.
unfold at_offset, offset_val.
set (ofs' := Ptrofs.add _ _). clearbody ofs'.
specialize  (H1 u1 u2 ofs'
                 (value_defined_not_volatile _ _ H3) H2 H3).
clear - H1.
set (y1 := data_at_rec sh1 _ _ _) in *.
set (y2 := data_at_rec sh2 _ _ _) in *.
apply derives_trans with ((y1*y2)*(x1*x2)). cancel.
eapply derives_trans. apply sepcon_derives. apply H1. apply TT_right.
rewrite prop_sepcon. Intros. apply prop_right; auto.
+
repeat change (struct_pred (a0 :: a1 :: m) ?P ?u ?p)
      with (P a0 (fst u) p * struct_pred (a1 :: m) P (snd u) p).
inv IH.
specialize (IHm _ H4).
destruct u1 as [v1 u1], u2 as [v2 u2].
destruct H2 as [H2v H2], H3 as [H3v H3].
specialize (IHm u1 u2 H2 H3).
clear H2 H3.
unfold snd. unfold fst.
match goal with |- ?a * ?b * (?c * ?d) |-- _ => 
   apply derives_trans with ((a*c)*(b*d)); [cancel | ]
end.
apply derives_trans with (!!(v1=v2) * !!(u1=u2)).
apply sepcon_derives; auto.
unfold field_atx.
rewrite !withspacer_spacer.
rewrite !spacer_memory_block by (simpl; auto).
set (x1 := memory_block sh1 _ _).
set (x2 := memory_block sh2 _ _).
clearbody x1 x2.
unfold at_offset, offset_val.
set (ofs' := Ptrofs.add _ _). clearbody ofs'. 
specialize (H1 v1 v2 ofs').
match goal with |- ?a * ?b * (?c * ?d) |-- _ => 
   apply derives_trans with ((a*c)*(b*d)); [cancel | ]
end.
apply derives_trans with (TT * !!(v1=v2)).
apply sepcon_derives; auto.
apply H1; auto.
eapply value_defined_not_volatile; eauto.
rewrite (sepcon_comm TT), prop_sepcon.
normalize.
rewrite prop_sepcon.
rewrite (sepcon_comm TT), prop_sepcon.
normalize.
-
cbv zeta in IH.
clear H.
change (type_func _ _ _ _ _ ) with value_defined in *.
unfold aggregate_pred.union_pred.
rewrite value_defined_eq in H2, H3.
contradiction.
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
    rewrite sepcon_comm.
    etransitivity.
   apply (IH (get_member i (co_members (get_co id)))).
   apply in_get_member; auto.
    f_equal.
    apply JMeq_eq.
    apply (@proj_compact_prod_JMeq _ _ _ (fun it => reptype (field_type (name_member it) (co_members (get_co id)))) (fun it => reptype (field_type (name_member it) (co_members (get_co id))))); auto.
    apply in_get_member; auto.
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
    etransitivity.
   apply (IH (get_member i (co_members (get_co id)))); auto.
    f_equal.
    apply JMeq_eq.
    apply (@proj_compact_sum_JMeq _ _ _ (fun it => reptype (field_type (name_member it) (co_members (get_co id)))) (fun it => reptype (field_type (name_member it) (co_members (get_co id))))); auto.
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
     (v1 := Zrepeat (default_val t) (Z.max 0 z)); auto.
    rewrite memory_block_array_pred; auto.
    - apply Z.le_max_l.
    - rewrite (proj1 H2).
      symmetry; apply Zlength_repeat; auto.
      apply Z.le_max_l.
    - intros.
      rewrite at_offset_eq3.
      unfold offset_val; solve_mod_modulus.
      unfold Znth. rewrite if_false by lia.
      rewrite Z.sub_0_r.
      assert (value_fits t (nth (Z.to_nat i) (unfold_reptype v) (default_val t))).
      {
        destruct H2.
        rewrite Forall_forall in H5.
        apply H5.
        apply nth_In.
        apply Nat2Z.inj_lt.
        rewrite <- Zlength_correct, H2, Z2Nat.id by lia.
        lia.
      }
      apply IH; auto.
      * pose_size_mult cs t (0 :: i :: i + 1 :: Z.max 0 z :: nil).
         unfold sizeof in H; simpl in H; fold (sizeof t) in H;  lia.
      * eapply align_compatible_rec_Tarray_inv; eauto.
        apply range_max0; auto.
  + rewrite struct_pred_ext with
     (P1 := fun it _ p =>
              memory_block sh
               (field_offset_next cenv_cs (name_member it) (co_members (get_co id)) (co_sizeof (get_co id)) -
                  field_offset cenv_cs (name_member it) (co_members (get_co id)))
               (offset_val (field_offset cenv_cs (name_member it) (co_members (get_co id))) p))
     (v1 := (struct_default_val (co_members (get_co id))));
    [| apply get_co_members_no_replicate |].
   clear H4. assert (H4:=I).
    - change (sizeof ?A) with (expr.sizeof A) in *.
      rewrite memory_block_struct_pred.
      * rewrite sizeof_Tstruct; auto.
      * apply get_co_members_nil_sizeof_0.
      * eapply complete_Tstruct_plain; apply LEGAL_COSU.
      * apply get_co_members_no_replicate.
      * rewrite sizeof_Tstruct in H.
        pose proof co_consistent_sizeof cenv_cs (get_co id) (get_co_consistent id).
        erewrite complete_legal_cosu_type_Tstruct in H3 by exact LEGAL_COSU.
        unfold sizeof_composite in H3.
        rewrite plain_members_sizeof_struct by (eapply complete_Tstruct_plain; apply LEGAL_COSU).
        revert H3; pose_align_le; intros; lia.
      * rewrite sizeof_Tstruct in H.
        auto.
    - intros.
   clear H4. assert (H4:=I).
      change (sizeof ?A) with (expr.sizeof A) in *.
      pose proof get_co_members_no_replicate id as NO_REPLI.
      rewrite withspacer_spacer.
      simpl @fst.
      rewrite spacer_memory_block by (simpl; auto).
      rewrite at_offset_eq3.
      unfold offset_val; solve_mod_modulus.
      unfold struct_default_val.
      rewrite Forall_forall in IH.
      specialize (IH (get_member i (co_members (get_co id)))).
      spec IH; [apply in_get_member; auto |].
      apply struct_Prop_proj with (i := i) (d:= d0) in H2; auto.
      rewrite IH; auto.
      * 
      rewrite name_member_get in *.
       rewrite Z.add_assoc, sepcon_comm.
       rewrite <- memory_block_split by (pose_field; lia).
        f_equal; lia.
      * rewrite name_member_get in *.
         apply complete_legal_cosu_type_field_type; auto.
          eapply complete_Tstruct_plain; apply LEGAL_COSU. 
      * rewrite name_member_get in *; 
         simpl fst. pose_field; lia.
      * rewrite name_member_get in *; 
         eapply align_compatible_rec_Tstruct_inv'; eauto.
  + assert (co_members (get_co id) = nil \/ co_members (get_co id) <> nil)
      by (clear; destruct (co_members (get_co id)); [left | right]; congruence).
       clear H4. pose proof I.
    destruct H3.
    - change (sizeof ?A) with (expr.sizeof A) in *.
      rewrite sizeof_Tunion.
      rewrite (get_co_members_nil_sizeof_0 _ H3).
      forget (unfold_reptype v) as v'; simpl in v'.
      generalize (unfold_reptype (default_val (Tunion id a)));
      clear H2; revert v'; rewrite H3 in *;
      intros.
      simpl.
      rewrite memory_block_zero.
      normalize.
    - change (sizeof ?A) with (expr.sizeof A) in *.
      rewrite union_pred_ext with
       (P1 := fun it _ => memory_block sh (co_sizeof (get_co id)))
       (v1 := (unfold_reptype v));
      [| apply get_co_members_no_replicate | reflexivity |].
      * rewrite memory_block_union_pred by (apply get_co_members_nil_sizeof_0).
        rewrite sizeof_Tunion.
        auto.
      * intros.
        pose proof get_co_members_no_replicate id as NO_REPLI.
        pose proof @compact_sum_inj_in _ _ (co_members (get_co id)) _ _ _ H5.
        apply in_map with (f := name_member) in H7; rewrite name_member_get in H7.
        rewrite withspacer_spacer.
        simpl @fst.
        rewrite spacer_memory_block by (simpl; auto).
        unfold offset_val; solve_mod_modulus.
        rewrite Forall_forall in IH.
        specialize (IH (get_member i (co_members (get_co id)))).
        spec IH; [apply in_get_member; auto |].
        apply union_Prop_proj with (i := i) (d := d0) in H2; auto.
        rewrite IH; auto; rewrite ?name_member_get in *.
        { rewrite sepcon_comm, <- memory_block_split by (pose_field; lia).
          f_equal; f_equal; lia.
        } {
          apply complete_legal_cosu_type_field_type; auto.
          eapply complete_Tunion_plain; apply LEGAL_COSU. 
        } {
          simpl fst; pose_field; lia.
        } {
          eapply align_compatible_rec_Tunion_inv'; eauto.
        }
Qed.

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
    revert v1' H1;
      rewrite (co_members_get_co_change_composite _ H0);
    intros.
    assert (NOREPET := @get_co_members_no_replicate cs_to id).
    unfold reptype_structlist in *.
    pose proof (fun i => field_offset_change_composite _ i H0) as HH0.
    pose proof (fun i => field_offset_next_change_composite _ i H0) as HH1.
    apply members_spec_change_composite in H0.
    forget (co_members (@get_co cs_to id)) as m.
    apply struct_pred_ext; [assumption |].
    intros.
    f_equal; [f_equal | | f_equal ]; auto.
    - apply sizeof_change_composite; auto.
      rewrite Forall_forall in H0.
      apply H0. apply in_get_member; auto.
    - clear HH0 HH1.
      pose proof in_get_member _ _ H.
      rewrite Forall_forall in IH, H0.
      specialize (IH _ H2); pose proof (H0 _ H2).
      apply IH; auto.
      apply (@proj_struct_JMeq i m
          (fun it : member => @reptype cs_from (field_type (name_member it) m)) 
          (fun it : member => @reptype cs_to (field_type (name_member it) m))); auto.
      intros. 
      rewrite reptype_change_composite; [reflexivity |].
      apply H0.
       apply in_get_member; auto.
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
    revert v1' H1;
      rewrite (co_members_get_co_change_composite _ H0);
    intros.
    assert (NOREPET := @get_co_members_no_replicate cs_to id).
    unfold reptype_structlist in *.
    assert (H0'' := co_sizeof_get_co_change_composite _ H0).
    apply members_spec_change_composite in H0.
    forget (co_members (@get_co cs_to id)) as m.
    apply union_pred_ext; [assumption | | ].
    {
      apply members_union_inj_JMeq; auto.
      intros.
      rewrite reptype_change_composite; [reflexivity |].
      pose proof in_get_member _ _ H.
      rewrite Forall_forall in H0.
      apply H0; auto.
    }
    intros.
    f_equal.
    - apply sizeof_change_composite; auto.
      rewrite Forall_forall in H0.
      apply H0.
      apply compact_sum_inj_in in H.
      auto.
    - auto. 
    - unfold reptype_unionlist.
      apply compact_sum_inj_in in H2.
      rewrite Forall_forall in IH, H0.
      specialize (IH _ H2); pose proof (H0 _ H2).
      apply IH; auto.
      apply (@proj_union_JMeq i _ 
          (fun it : member => @reptype cs_from (field_type (name_member it) m)) 
          (fun it : member => @reptype cs_to (field_type (name_member it) m))); auto.
      intros.
      rewrite reptype_change_composite; [reflexivity |].
      apply H0.
      apply in_get_member; auto.
Qed.

(**** tactics for value_fits  ****)

Lemma value_fits_Tstruct:
  forall {cs: compspecs} t (v: reptype t) i a m v2 r,
  t = Tstruct i a ->
  m = co_members (get_co i)  ->
  JMeq (@unfold_reptype cs t v) v2 ->
  r =struct_Prop m
          (fun it => value_fits (field_type (name_member it) m))  v2 ->
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
          (fun it => value_fits (field_type (name_member it) m))  v2 ->
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
 (simple_if_tac; auto; apply prop_ext; tauto).
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
 (simple_if_tac; auto; auto; apply prop_ext; tauto).
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
 (simple_if_tac; auto; apply prop_ext; tauto).
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
rewrite Z.max_r by lia. auto.
Qed.

Ltac cleanup_unfold_reptype :=
    match goal with |- JMeq (unfold_reptype ?A) _ =>
                 instantiate (1:=A); apply JMeq_refl
    end.

Ltac simplify_value_fits' :=
first
 [erewrite value_fits_Tstruct;
    [ | reflexivity
    | reflexivity
    | cleanup_unfold_reptype
    | reflexivity];
    simpl struct_Prop
 |erewrite value_fits_Tarray;
    [ | reflexivity
    | cleanup_unfold_reptype
    | repeat subst_any; try computable; lia
    | reflexivity
    ]
 | erewrite value_fits_by_value_defined;
   [ | reflexivity
   | repeat subst_any; clear; simpl; intro; discriminate
   | reflexivity
   | reflexivity
   ]
 | rewrite value_fits_by_value_Vundef;
   [ | reflexivity | reflexivity
   ]
 | erewrite value_fits_by_value;
   [ | reflexivity
   | reflexivity
   | reflexivity
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

Lemma value_defined_tarray {cs: compspecs}:
 forall t n vl,
  Zlength vl = n -> 
  Forall (value_defined t) vl ->
  value_defined (tarray t n) vl.
Proof.
intros.
red. rewrite type_induction.type_func_eq. unfold tarray.
split; auto.
subst.
unfold unfold_reptype. simpl. rep_lia.
Qed.

