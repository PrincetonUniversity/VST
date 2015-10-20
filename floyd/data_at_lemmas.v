Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.type_induction.
Require Import floyd.nested_pred_lemmas.
Require Import floyd.mapsto_memory_block.
Require floyd.aggregate_pred. Import floyd.aggregate_pred.aggregate_pred.
Import floyd.aggregate_pred.auxiliary_pred.
Require Import floyd.reptype_lemmas.
Require Import floyd.jmeq_lemmas.
Require Import floyd.sublist.

Opaque alignof.

Local Open Scope logic.

Arguments align !n !amount / .
Arguments Z.max !n !m / .

Definition offset_in_range ofs p :=
  match p with
  | Vptr b iofs => 0 <= Int.unsigned iofs + ofs <= Int.modulus
  | _ => True
  end.

Definition offset_strict_in_range ofs p :=
  match p with
  | Vptr b iofs => 0 <= Int.unsigned iofs + ofs < Int.modulus
  | _ => True
  end.

(************************************************

Definition of data_at 

Always assume in arguments of data_at', array_at', sfieldlist_at', ufieldlist_
at' has argument pos with alignment criterion. So, spacers are only added after
fields of structs or unions.

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

Definition data_at': forall t, reptype t -> val -> mpred :=
  func_type (fun t => reptype t -> val -> mpred)
    (fun t v p =>
       if type_is_volatile t
       then memory_block sh (sizeof cenv_cs t) p
       else mapsto sh t p (repinject t v))
    (fun t n a P v => array_pred (default_val t) 0 n (fun i v => at_offset (P v) (sizeof cenv_cs t * i)) (unfold_reptype v))
    (fun id a P v => struct_data_at'_aux sh (co_members (get_co id)) (co_members (get_co id)) (co_sizeof (get_co id)) P (unfold_reptype v))
    (fun id a P v => union_data_at'_aux sh (co_members (get_co id)) (co_members (get_co id)) (co_sizeof (get_co id)) P (unfold_reptype v)).

Lemma data_at'_ind: forall t v,
  data_at' t v =
  match t return REPTYPE t -> val -> mpred with
  | Tvoid
  | Tfunction _ _ _ => fun _ _ => FF
  | Tint _ _ _
  | Tfloat _ _
  | Tlong _ _
  | Tpointer _ _ => fun v p => 
                      if type_is_volatile t
                      then memory_block sh (sizeof cenv_cs t) p
                      else mapsto sh t p v
  | Tarray t0 n a => array_pred (default_val t0) 0 n (fun i v => at_offset (data_at' t0 v) (sizeof cenv_cs t0 * i))
  | Tstruct id a => struct_pred (co_members (get_co id))
                      (fun it v => withspacer sh
                        (field_offset cenv_cs (fst it) (co_members (get_co id)) + sizeof cenv_cs (field_type (fst it) (co_members (get_co id))))
                        (field_offset_next cenv_cs (fst it) (co_members (get_co id)) (co_sizeof (get_co id)))
                        (at_offset (data_at' (field_type (fst it) (co_members (get_co id))) v) (field_offset cenv_cs (fst it) (co_members (get_co id)))))
  | Tunion id a => union_pred (co_members (get_co id))
                     (fun it v => withspacer sh
                      (sizeof cenv_cs (field_type (fst it) (co_members (get_co id))))
                      (co_sizeof (get_co id))
                      (data_at' (field_type (fst it) (co_members (get_co id))) v))
  end (unfold_reptype v).
Proof.
  intros.
  unfold data_at' at 1.
  rewrite func_type_ind.
  destruct t; auto;
  try solve [destruct (readable_share_dec sh); reflexivity];
  try solve [
  match goal with
  | |- appcontext [repinject ?tt] => 
    rewrite (repinject_unfold_reptype tt); auto
  end].
  + rewrite <- struct_data_at'_aux_spec; reflexivity.
  + rewrite <- union_data_at'_aux_spec; reflexivity.
Qed.

End WITH_SHARE.

Lemma data_at'_type_changable: forall (sh: Share.t) (t1 t2: type) v1 v2,
  t1 = t2 ->
  JMeq v1 v2 ->
  data_at' sh t1 v1 = data_at' sh t2 v2.
Proof.
  intros.
  subst t2.
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
  erewrite data_at'_type_changable; [| exact H| exact H0].
  rewrite H.
  reflexivity.
Qed.
*)
Lemma by_value_default_val: forall t:type, 
  type_is_by_value t = true -> JMeq (default_val t) Vundef.
Proof.
  intros.
  destruct t; try inversion H; try tauto.
Qed.

(************************************************

Transformation between data_at/data_at_ and mapsto.

************************************************)

Lemma by_value_reptype: forall t, type_is_by_value t = true -> reptype t = val.
Proof.
  intros.
  destruct t; simpl in H; try inversion H; tauto.
Qed.

Lemma by_value_data_at': forall sh t v p,
  type_is_by_value t = true ->
  type_is_volatile t = false ->
  data_at' sh t v p = mapsto sh t p (repinject t v).
Proof.
  intros.
  rewrite data_at'_ind; destruct t; try solve [inversion H]; rewrite H0;
  match goal with
  | |- appcontext [repinject ?tt] => 
    rewrite (repinject_unfold_reptype tt); auto
  end.
Qed.

Lemma by_value_data_at'_default_val: forall sh t p,
  type_is_by_value t = true ->
  legal_alignas_type t = true ->
  size_compatible t p ->
  align_compatible t p ->
  data_at' sh t (default_val t) p = memory_block sh (sizeof cenv_cs t) p.
Proof.
  intros.
  rewrite data_at'_ind; destruct t; try solve [inversion H];
  match goal with
  | |- appcontext [type_is_volatile ?tt] => 
    destruct (type_is_volatile tt) eqn:HH; auto;
    rewrite <- (repinject_unfold_reptype tt); auto
  end;
  symmetry;
  cbv [repinject default_val reptype_gen func_type func_type_rec rank_type type_is_by_value];
  rewrite memory_block_mapsto_ by auto; unfold mapsto_; 
    try rewrite if_true by auto; auto.
Qed.

Lemma by_value_data_at'_default_val2: forall sh t b ofs,
  type_is_by_value t = true ->
  legal_alignas_type t = true ->
  0 <= ofs /\ ofs + sizeof cenv_cs t <= Int.modulus ->
  (alignof cenv_cs t | ofs) ->
  data_at' sh t (default_val t) (Vptr b (Int.repr ofs)) =
  memory_block sh (sizeof cenv_cs t) (Vptr b (Int.repr ofs)).
Proof.
  intros.
  apply by_value_data_at'_default_val; auto.
  + unfold size_compatible.
    solve_mod_modulus.
    pose_mod_le ofs.
    omega.
  + unfold align_compatible.
    solve_mod_modulus.
    pose_size_mult cenv_cs t (0 :: 1 :: nil).
    apply arith_aux04; auto; omega.
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

Lemma uncompomize_by_value_data_at_: forall sh e t p,
  type_is_by_value (uncompomize e t) = true ->
  data_at_ sh t p =
  !! field_compatible (uncompomize e t) nil p && mapsto_ sh (uncompomize e t) p.
Proof.
  intros.
  unfold data_at_, mapsto_.
  apply uncompomize_by_value_data_at; [exact H|].
  erewrite <- uncompomize_default_val.
  apply by_value_default_val.
  exact H.
Qed.

Lemma lifted_by_value_data_at: forall sh t v p,
  type_is_by_value t = true ->
  `(data_at sh t) (`(valinject t) v) p =
  local (`(field_compatible t nil) p) && `(mapsto sh t) p v.
Proof.
  unfold liftx, lift; simpl; intros; extensionality rho.
  apply by_value_data_at; [|apply valinject_JMeq]; assumption.
Qed.

Lemma lifted_uncompomize_by_value_data_at: forall sh e t v p,
  type_is_by_value (uncompomize e t) = true ->
  `(data_at sh t) (`(valinject t) v) p =
  local (`(field_compatible (uncompomize e t) nil) p) &&
  `(mapsto sh (uncompomize e t)) p v.
Proof.
  unfold liftx, lift; simpl; intros; extensionality rho.
  apply uncompomize_by_value_data_at;
  [|erewrite <- uncompomize_valinject; apply valinject_JMeq]; eassumption.
Qed.

Lemma lifted_by_value_data_at_: forall sh t p,
  type_is_by_value t = true ->
  `(data_at_ sh t) p = local (`(field_compatible t nil) p) && `(mapsto_ sh t) p.
Proof.
  unfold liftx, lift; simpl; intros; extensionality rho.
  apply by_value_data_at_; assumption.
Qed.

Lemma lifted_uncompomize_by_value_data_at_: forall sh e t p,
  type_is_by_value (uncompomize e t) = true ->
  `(data_at_ sh t) p =
  local (`(field_compatible (uncompomize e t) nil) p) &&
  `(mapsto_ sh (uncompomize e t)) p.
Proof.
  unfold liftx, lift; simpl; intros; extensionality rho.
  apply uncompomize_by_value_data_at_; assumption.
Qed.
*)
(************************************************

Transformation between data_at and data_at'. This is used in transformation
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
  0 <= pos /\ pos + sizeof cenv_cs t <= Int.modulus - Int.unsigned i ->
  Int.unsigned (Int.add i (Int.repr pos)) + sizeof cenv_cs t <= Int.modulus.
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
  0 <= pos /\ pos + sizeof cenv_cs t <= Int.modulus - Int.unsigned i ->
  (alignof cenv_cs t | Int.unsigned i) ->
  (alignof cenv_cs t | pos) ->
  (alignof cenv_cs t | Int.unsigned (Int.add i (Int.repr pos))).
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
Lemma Znth_nil: forall {A} n (d: A), Znth n nil d = d.
Proof.
  intros.
  unfold Znth.
  if_tac; auto.
  simpl.
  destruct (Z.to_nat n); auto.
Qed.

Lemma offset_val_zero_Vptr: forall b i, offset_val (Int.repr 0) (Vptr b i) = Vptr b i.
Proof.
  intros.
  unfold offset_val, Int.add.
  change (Int.unsigned (Int.repr 0)) with 0.
  rewrite Z.add_0_r.
  rewrite Int.repr_unsigned.
  reflexivity.
Qed.

Ltac AUTO_IND :=
  match goal with
  | H: legal_alignas_type (Tarray ?t ?n ?a) = true |- legal_alignas_type ?t = true =>
    unfold legal_alignas_type in H;
    apply nested_pred_Tarray in H;
    exact H
  | H: legal_cosu_type (Tarray ?t ?n ?a) = true |- legal_cosu_type ?t = true =>
    unfold legal_cosu_type in H;
    apply nested_pred_Tarray in H;
    exact H
  | H: complete_type ?env (Tarray ?t ?n ?a) = true |- complete_type ?env ?t = true =>
    simpl in H; auto
  | H: (alignof cenv_cs (Tarray ?t ?z ?a) | ?ofs)
    |- (alignof cenv_cs ?t | ?ofs + _) =>
    apply Z.divide_add_r;
    [ eapply Z.divide_trans; [eapply alignof_divide_alignof_Tarray |]; eauto
    | apply Z.divide_mul_l; erewrite legal_alignas_type_Tarray by eauto;
      apply legal_alignas_sizeof_alignof_compat; AUTO_IND]
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
  | H: (alignof cenv_cs (Tstruct ?id ?a) | ?ofs)
    |- (alignof cenv_cs (field_type ?i (co_members (get_co ?id))) | ?ofs + _) =>
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
  | H: (alignof cenv_cs (Tunion ?id ?a) | ?ofs)
    |- (alignof cenv_cs (field_type ?i (co_members (get_co ?id))) | ?ofs) =>
    eapply Z.divide_trans; [apply alignof_field_type_divide_alignof; auto |];
    eapply Z.divide_trans; [apply legal_alignas_type_Tunion; eauto | auto]
  end.

Unset Ltac Debug.

Lemma legal_alignas_array_size:
  forall t z a, legal_alignas_type (Tarray t z a) = true -> 0 <= z.
Proof.
intros.
    unfold legal_alignas_type, nested_pred in H. simpl in H.
    rewrite andb_true_iff in H; destruct H as [H _].
    unfold local_legal_alignas_type in H; simpl in H.
    rewrite andb_true_iff in H; destruct H as [_ H].
    destruct (attr_alignas (attr_of_type t)); inv H.
    apply Zle_bool_imp_le; auto. 
Qed.

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

Lemma memory_block_data_at'_default_val: forall sh t b ofs
  (LEGAL_ALIGNAS: legal_alignas_type t = true)
  (LEGAL_COSU: legal_cosu_type t = true) (* isn't this subsumed by complete_type ?*)
  (COMPLETE: complete_type cenv_cs t = true),
  0 <= ofs /\ ofs + sizeof cenv_cs t <= Int.modulus ->
  sizeof cenv_cs t < Int.modulus -> (* check why need this *)
  (alignof cenv_cs t | ofs) ->
  data_at' sh t (default_val t) (Vptr b (Int.repr ofs)) =
    memory_block sh (sizeof cenv_cs t) (Vptr b (Int.repr ofs)).
Proof.
  intros sh t.
  type_induction t; intros;
  try solve [inversion COMPLETE];
  try solve [apply by_value_data_at'_default_val2; auto];
  rewrite data_at'_ind.
  + rewrite (default_val_ind (Tarray t z a)).
    rewrite unfold_fold_reptype.
    rewrite array_pred_ext with
     (P1 := fun i _ p => memory_block sh (sizeof cenv_cs t)
                          (offset_val (Int.repr (sizeof cenv_cs t * i)) p))
     (v1 := list_repeat (Z.to_nat z) (default_val t)); auto.
    pose proof (legal_alignas_array_size _ _ _ LEGAL_ALIGNAS).
    rewrite memory_block_array_pred; auto.
    - simpl sizeof; rewrite Z.max_r by omega; auto.
    - simpl in H; rewrite Z.max_r in H by omega; auto.
    - simpl in H0; rewrite Z.max_r in H0 by omega; auto.
    - intros.
      rewrite at_offset_eq3.
      unfold offset_val; solve_mod_modulus.
      unfold Znth. rewrite if_false by omega.
      rewrite nth_list_repeat.
      simpl sizeof in H, H0;
      rewrite Z.max_r in H, H0 by omega.
      apply IH; try AUTO_IND;
      pose_size_mult cenv_cs t (0 :: i :: i + 1 :: z :: nil); omega.
  + rewrite default_val_ind.
    rewrite unfold_fold_reptype.
    rewrite struct_pred_ext with
     (P1 := fun it _ p =>
              memory_block sh 
               (field_offset_next cenv_cs (fst it) (co_members (get_co id)) (co_sizeof (get_co id)) -
                  field_offset cenv_cs (fst it) (co_members (get_co id)))
               (offset_val (Int.repr (field_offset cenv_cs (fst it) (co_members (get_co id)))) p))
     (v1 := (struct_default_val (co_members (get_co id))));
    [| apply get_co_members_no_replicate |].
    - rewrite memory_block_struct_pred.
      * rewrite sizeof_Tstruct; auto.
      * apply get_co_members_nil_sizeof_0.
      * apply get_co_members_no_replicate.
      * rewrite sizeof_Tstruct in H0.
        pose proof co_consistent_sizeof cenv_cs (get_co id) (get_co_consistent id).
        erewrite legal_cosu_type_Tstruct in H2 by eauto.
        unfold sizeof_composite in H2.
        revert H2; pose_align_le; intros; omega.
      * rewrite sizeof_Tstruct in H.
        auto.
    - intros.
      pose proof get_co_members_no_replicate id as NO_REPLI.
      rewrite withspacer_spacer.
      simpl.
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
      rewrite IH by (try unfold fst; try AUTO_IND; try (pose_field; omega)).
      rewrite Z.add_assoc, sepcon_comm, <- memory_block_split by (pose_field; omega).
      f_equal; omega.
  + assert (co_members (get_co id) = nil \/ co_members (get_co id) <> nil)
      by (destruct (co_members (get_co id)); [left | right]; congruence).
    destruct H2.
    - rewrite sizeof_Tunion.
      rewrite (get_co_members_nil_sizeof_0 _ H2).
      generalize (unfold_reptype (default_val (Tunion id a)));
      rewrite H2 in *;
      intros.
      simpl.
      rewrite memory_block_zero.
      normalize.
    - rewrite default_val_ind.
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
        apply in_map with (f := fst) in H5; unfold fst in H5.
        rewrite withspacer_spacer.
        simpl.
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
        rewrite IH; (try unfold fst; try AUTO_IND; try (pose_field; omega)).
        rewrite sepcon_comm, <- memory_block_split by (pose_field; omega).
        f_equal; f_equal; omega.
Qed.

(*
Lemma align_1_memory_block_data_at_: forall (sh : share) (t : type),
  legal_alignas_type t = true ->
  nested_legal_fieldlist t = true ->
  nested_non_volatile_type t = true ->
  alignof t = 1%Z ->
  (sizeof t < Int.modulus)%Z ->
  memory_block sh (Int.repr (sizeof t)) = data_at_ sh t.
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
Lemma data_at'_readable:
  forall sh t v p, data_at' sh t v p |-- !! readable_share sh.
Proof.
intros sh t.
type_induction t; intros;
rewrite data_at'_ind; try apply FF_left.
if_tac.
+ simpl. destruct i; simpl.
SearchAbout memory_block.
rewrite memory_block_eq.
saturate_local.
simpl.
*)

Lemma data_at'_data_at'_ : forall sh t v b ofs
  (LEGAL_ALIGNAS: legal_alignas_type t = true)
  (LEGAL_COSU: legal_cosu_type t = true)
  (COMPLETE: complete_type cenv_cs t = true),
  0 <= ofs /\ ofs + sizeof cenv_cs t <= Int.modulus ->
  sizeof cenv_cs t < Int.modulus -> (* check why need this *)
  (alignof cenv_cs t | ofs) ->
  data_at' sh t v (Vptr b (Int.repr ofs)) |-- data_at' sh t (default_val t) (Vptr b (Int.repr ofs)).
Proof.
  intros sh t.
  type_induction t; intros;
  try solve [inversion COMPLETE];
  try solve [rewrite !data_at'_ind; try (if_tac; auto);
  try solve [rewrite default_val_ind, unfold_fold_reptype; apply mapsto_mapsto_]].
  + rewrite !data_at'_ind.
    apply array_pred_ext_derives. rewrite default_val_ind.
    intros.
    rewrite !at_offset_eq3.
    rewrite default_val_ind with (t0 := (Tarray t z a)), unfold_fold_reptype.
    simpl sizeof in H, H0;
    rewrite Z.max_r in H, H0 by omega.
    eapply derives_trans.
    apply IH; try AUTO_IND;
    pose_size_mult cenv_cs t (0 :: i :: i + 1 :: z :: nil); omega.
    apply derives_refl'. f_equal. unfold Znth. rewrite if_false by omega.
    rewrite nth_list_repeat'; auto.
    apply Nat2Z.inj_lt. rewrite !Z2Nat.id by omega. omega.
  + rewrite !data_at'_ind.
    rewrite default_val_ind, unfold_fold_reptype.
    assert (members_no_replicate (co_members (get_co id)) = true) as NO_REPLI
      by apply get_co_members_no_replicate.
    apply struct_pred_ext_derives; [auto |].
    intros.
    rewrite !withspacer_spacer.
    simpl.
    apply sepcon_derives; [auto |].
    rewrite !at_offset_eq3.
    rewrite Forall_forall in IH.
    specialize (IH (i, (field_type i (co_members (get_co id))))).
    spec IH; [apply in_members_field_type; auto |].
    unfold snd in IH.
    unfold struct_default_val.
    unfold proj_struct.
    rewrite compact_prod_proj_gen by (apply in_members_field_type; auto).
    apply IH; try unfold fst; try AUTO_IND; try (pose_field; omega).
  + assert (co_members (get_co id) = nil \/ co_members (get_co id) <> nil)
      by (destruct (co_members (get_co id)); [left | right]; congruence).
    destruct H2.
    - rewrite !data_at'_ind.
      generalize (unfold_reptype v) (unfold_reptype (default_val (Tunion id a))); rewrite H2; intros.
      auto.
    - rewrite data_at'_ind.
      rewrite memory_block_data_at'_default_val by auto.
      eapply derives_trans.
      * assert (members_no_replicate (co_members (get_co id)) = true) as NO_REPLI
          by apply get_co_members_no_replicate.
        apply union_pred_ext_derives with
          (P1 := fun _ _ => memory_block sh (sizeof cenv_cs (Tunion id a)));
          [auto | reflexivity | ].
        intros.
        clear H4.
        pose proof @compact_sum_inj_in _ _ (co_members (get_co id)) (unfold_reptype v) _ _ H3.
        apply in_map with (f := fst) in H4; unfold fst in H4.
        rewrite withspacer_spacer, sizeof_Tunion.
        simpl.
        pattern (co_sizeof (get_co id)) at 2;
        replace (co_sizeof (get_co id)) with (sizeof cenv_cs (field_type i (co_members (get_co id))) +
          (co_sizeof (get_co id) - sizeof cenv_cs (field_type i (co_members (get_co id))))) by omega.
        rewrite sepcon_comm.
        rewrite memory_block_split by (pose_field; omega).
        apply sepcon_derives; [| rewrite spacer_memory_block by (simpl; auto);
                                 unfold offset_val; solve_mod_modulus; auto ].
        rewrite <- memory_block_data_at'_default_val; auto; try AUTO_IND; try (pose_field; omega).
        rewrite Forall_forall in IH.
        specialize (IH (i, (field_type i (co_members (get_co id))))).
        spec IH; [apply in_members_field_type; auto |].
        unfold snd in IH.
        apply IH; try AUTO_IND; try (pose_field; omega).
      * rewrite sizeof_Tunion.
        rewrite memory_block_union_pred by (apply get_co_members_nil_sizeof_0).
        auto.
Qed.

Definition tc_val' t v := v<>Vundef -> tc_val t v.

Definition value_fits (sh: bool): forall t, reptype t -> Prop :=
  func_type (fun t => reptype t -> Prop)
    (fun t v =>
       if type_is_volatile t then True else if sh then tc_val' t (repinject t v) else True)
    (fun t n a P v => Zlength (unfold_reptype v) =  Z.max 0 n /\ Forall P (unfold_reptype v))
    (fun id a P v => struct_value_fits_aux (co_members (get_co id)) (co_members (get_co id)) P (unfold_reptype v))
    (fun id a P v => union_value_fits_aux (co_members (get_co id)) (co_members (get_co id)) P (unfold_reptype v)).

Lemma value_fits_ind:
  forall sh t v, 
  value_fits sh t v = 
  match t as t0 return (reptype t0 -> Prop)  with
  | Tarray t' n a => fun v0 : reptype (Tarray t' n a) =>
    (fun v1 : reptype_array t' 0 n =>
     Zlength v1 = Z.max 0 n /\ Forall (value_fits sh t') v1)
      (unfold_reptype v0)
| Tstruct i a =>
    fun v0 : reptype (Tstruct i a) =>
     struct_Prop (co_members (get_co i))
       (fun it : ident * type =>
        value_fits sh (field_type (fst it) (co_members (get_co i)))) (unfold_reptype v0)
| Tunion i a =>
    fun v0 : reptype (Tunion i a) =>
     union_Prop (co_members (get_co i))
       (fun it : ident * type =>
        value_fits sh (field_type (fst it) (co_members (get_co i)))) (unfold_reptype v0)
  | t0 => fun v0: reptype t0 =>
             (if type_is_volatile t0
              then True
              else if sh then tc_val' t0 (repinject t0 v0) else True)
  end v.
Proof.
intros.
unfold value_fits.
rewrite func_type_ind.
destruct t; auto.
apply struct_value_fits_aux_spec.
apply union_value_fits_aux_spec.
Qed.

Lemma value_fits_type_changable: forall sh (t1 t2: type) v1 v2,
  t1 = t2 ->
  JMeq v1 v2 ->
  value_fits sh t1 v1 = value_fits sh t2 v2.
Proof.
  intros.
  subst t2.
  rewrite H0.
  reflexivity.
Qed.

Lemma empty_data_at': forall sh t v b ofs,
  legal_cosu_type t = true ->
  sizeof cenv_cs t = 0 ->
  data_at' sh t v (Vptr b (Int.repr ofs)) = emp.
Proof.
  intros ? ?.
  type_induction t; [| destruct i | | destruct f | | | | |]; intros; rewrite data_at'_ind;
  try solve [inversion H0].
  + apply Tarray_sizeof_0 in H0.
    destruct H0.
    - rewrite array_pred_ext with (P1 := fun _ _ _ => emp) (v1 := unfold_reptype v).
      * apply emp_array_pred.
      * intros.
        rewrite at_offset_eq.
        apply IH; auto.
    - apply array_pred_len_0; auto.
  + pose proof Tstruct_sizeof_0 id a H H0.
    rewrite struct_pred_ext with (P1 := fun _ _ _ => emp) (v1 := unfold_reptype v).
    - apply emp_struct_pred.
    - apply get_co_members_no_replicate.
    - intros.
      destruct (H1 i H2).
      rewrite Forall_forall in IH.
      specialize (IH (i, (field_type i (co_members (get_co id))))).
      spec IH; [apply in_members_field_type; auto |].
      autorewrite with at_offset_db.
      unfold fst, snd in *.
      rewrite H4, H3.
      rewrite memory_block_zero.
      rewrite IH by (auto; AUTO_IND).
      unfold offset_val; normalize.
  + assert (co_members (get_co id) = nil \/ co_members (get_co id) <> nil) as HH
      by (destruct (co_members (get_co id)); [left | right]; congruence).
    destruct HH as [HH | HH].
    - generalize (unfold_reptype v); rewrite HH; intros.
      simpl; auto.
    - pose proof Tunion_sizeof_0 id a H H0.
      rewrite union_pred_ext with (P1 := fun _ _ _ => emp) (v1 := unfold_reptype v).
      * apply emp_union_pred.
      * apply get_co_members_no_replicate.
      * intros; tauto.
      * intros.
        pose proof compact_sum_inj_in (unfold_reptype v) _ _ H2.
        unfold members_union_inj in *.
        apply in_map with (f := fst) in H4.
        specialize (H1 i H4).
        rewrite Forall_forall in IH.
        specialize (IH (i, (field_type i (co_members (get_co id))))).
        spec IH; [apply in_members_field_type; auto |].
        autorewrite with at_offset_db.
        unfold fst, snd in *.
        rewrite sizeof_Tunion in H0.
        rewrite H1, H0.
        rewrite memory_block_zero.
        rewrite IH by (auto; AUTO_IND).
        unfold offset_val; normalize.
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
  Focus 1. {
    unfold legal_alignas_type in H2.
    simpl in H2.
    rewrite andb_true_iff in H2.
    tauto.
  } Unfocus.
  assert (alignof t | sizeof t * i).
  Focus 1. {
    apply Z.divide_mul_l.
    apply legal_alignas_sizeof_alignof_compat, H5.
  } Unfocus.
  rewrite !data_at'_at_offset with (pos := (sizeof t * i)%Z) by auto.
  rewrite !at_offset_eq by (rewrite <- data_at'_offset_zero; reflexivity).
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

Lemma data_at_tint: forall sh v2 v1,
  data_at sh tint v2 v1 = mapsto sh tint v1 v2.
Proof.
  intros.
  unfold data_at, data_at'.
  simpl.
  apply pred_ext; normalize.
  apply andp_right; [|normalize].
  rewrite mapsto_isptr.
  unfold mapsto. simpl.
  unfold address_mapsto, res_predicates.address_mapsto, size_compatible, align_compatible.
  assert (legal_alignas_type tint = true) by reflexivity.
  assert (nested_legal_fieldlist tint = true) by reflexivity.
  destruct v1; normalize.
  eapply derives_trans with (!!(Int.unsigned i + sizeof tint <= Int.modulus /\
          (alignof tint | Int.unsigned i))); [| normalize].
  change (@predicates_hered.exp compcert_rmaps.RML.R.rmap
      compcert_rmaps.R.ag_rmap) with (@exp mpred Nveric).
  change (@predicates_hered.andp compcert_rmaps.RML.R.rmap
      compcert_rmaps.R.ag_rmap) with (@andp mpred Nveric).
  change (@predicates_hered.prop compcert_rmaps.RML.R.rmap
      compcert_rmaps.R.ag_rmap) with (@prop mpred Nveric).
  change (sizeof tint) with 4.
  change (alignof tint) with 4.
  change (Memdata.align_chunk Mint32) with 4.
  assert ((4 | Int.unsigned i) -> Int.unsigned i + 4 <= Int.modulus).
  Focus 1. {
    intros.
    destruct H2.
    pose proof Int.unsigned_range i.
    rewrite H2 in *.
    change Int.modulus with (1073741824 * 4)%Z in *.
    destruct H3 as [_ ?].
    rewrite Zmult_succ_l_reverse.
    apply Zmult_le_compat_r; [| omega].
    destruct (zle (Z.succ x) 1073741824); auto.
    assert (1073741824 <= x) by omega.
    apply Zmult_le_compat_r with (p := 4) in H4; [| omega].
    omega.
  } Unfocus.
  eapply orp_left; normalize; apply prop_right.
Qed.

*)

End CENV.



(**** tactics for value_fits  ****)

Lemma value_fits_Tstruct:
  forall {cs: compspecs} sh t (v: reptype t) i a m v2 r,
  t = Tstruct i a ->
  m = co_members (get_co i)  ->
  JMeq (@unfold_reptype cs t v) v2 ->
  r =struct_Prop m 
          (fun it => value_fits sh (fieldlist.field_type2 (fst it) m))  v2 ->
  value_fits sh t v = r.
Proof.
intros.
subst.
rewrite value_fits_ind; simpl.
f_equal.
apply JMeq_eq in H1. auto.
Qed.

Lemma value_fits_by_value_defined:
  forall {cs: compspecs} (sh: bool) t t' v r,
   type_is_by_value t = true ->  
   repinject t v <> Vundef  ->
   t = t' ->
   (r = if type_is_volatile t' then True
       else if sh then tc_val t' (repinject t v) else True) ->
   value_fits sh t v = r. 
Proof.
intros. subst t' r.
rewrite value_fits_ind.
unfold tc_val'.
destruct t; inv H;
 (if_tac; auto; if_tac; auto; apply prop_ext; intuition).
Qed.

Lemma value_fits_by_value_Vundef:
  forall {cs: compspecs} (sh: bool) t v,
   type_is_by_value t = true ->  
   repinject t v = Vundef  ->
   value_fits sh t v = True. 
Proof.
intros.
rewrite value_fits_ind.
unfold tc_val'.
destruct t; inv H;
 (if_tac; auto; if_tac; auto; apply prop_ext; intuition).
Qed.

Lemma value_fits_by_value:
  forall {cs: compspecs} (sh: bool) t t' v r,
   type_is_by_value t = true ->
   t = t' ->  
   (r = if type_is_volatile t then True
       else if sh then tc_val' t' (repinject t v) else True) ->
   value_fits sh t v = r. 
Proof.
intros. subst r t'.
rewrite value_fits_ind.
unfold tc_val'.
destruct t; inv H;
 (if_tac; auto; if_tac; auto; apply prop_ext; intuition).
Qed.

Lemma value_fits_Tarray:
  forall {cs: compspecs} (sh: bool) t (v: reptype t) t' n a 
    (v' : list (reptype t')) r,
  t = (Tarray t' n a) ->
  JMeq (unfold_reptype v) v' ->
  n >= 0 ->
  r = (Zlength v' = n /\ Forall (value_fits sh t') v') ->
  value_fits sh t v =r.
Proof.
intros.
subst. rewrite value_fits_ind.
apply JMeq_eq in H0. rewrite H0.
rewrite Z.max_r by omega. auto.
Qed.

Ltac cleanup_unfold_reptype :=
    match goal with |- JMeq (unfold_reptype ?A) _ =>
                 instantiate (1:=A); reflexivity
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
 cbv beta.

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
