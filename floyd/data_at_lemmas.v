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
Require Import Coq.Logic.JMeq.

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
at' has argument pos with alignment criterian. So, spacers are only added after
fields of structs or unions.

************************************************)

Section CENV.

Context {cs: compspecs}.
Context {csl: compspecs_legal cs}.

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
       then memory_block sh (Int.repr (sizeof cenv_cs t)) p
       else mapsto sh t p (repinject t v))
    (fun t n a P v => array_pred 0 n (default_val t) (fun i v => at_offset (P v) (sizeof cenv_cs t * i)) (unfold_reptype v))
    (fun id a P v => struct_data_at'_aux sh (co_members (get_co id)) (co_members (get_co id)) (co_sizeof (get_co id)) P (unfold_reptype v))
    (fun id a P v => union_data_at'_aux sh (co_members (get_co id)) (co_sizeof (get_co id)) P (unfold_reptype v)).

Notation REPTYPE t :=
  match t return Type with
  | Tvoid
  | Tfunction _ _ _ => unit
  | Tint _ _ _
  | Tlong _ _
  | Tfloat _ _
  | Tpointer _ _ => val
  | Tarray t0 _ _ => list (reptype t0)
  | Tstruct id _ => reptype_structlist (co_members (get_co id))
  | Tunion id _ => reptype_unionlist (co_members (get_co id))
  end.

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
                      then memory_block sh (Int.repr (sizeof cenv_cs t)) p
                      else mapsto sh t p v
  | Tarray t0 n a => array_pred 0 n (default_val t0) (fun i v => at_offset (data_at' t0 v) (sizeof cenv_cs t0 * i))
  | Tstruct id a => struct_pred (co_members (get_co id))
                      (fun it v => withspacer sh
                        (field_offset cenv_cs (fst it) (co_members (get_co id)) + sizeof cenv_cs (snd it))
                        (field_offset_next cenv_cs (fst it) (co_members (get_co id)) (co_sizeof (get_co id)))
                        (at_offset (data_at' (snd it) v) (field_offset cenv_cs (fst it) (co_members (get_co id)))))
  | Tunion id a => union_pred (co_members (get_co id))
                     (fun it v => withspacer sh
                      (sizeof cenv_cs (snd it))
                      (co_sizeof (get_co id))
                      (data_at' (snd it) v))
  end (unfold_reptype v).
Proof.
  intros.
  unfold data_at' at 1.
  rewrite func_type_ind.
  destruct t; auto;
  try solve [
  match goal with
  | |- appcontext [repinject ?tt] => 
    rewrite (repinject_unfold_reptype tt); auto
  end].
  + rewrite <- struct_data_at'_aux_spec; reflexivity.
  + rewrite <- union_data_at'_aux_spec; reflexivity.
Qed.

(*
Definition data_at (sh: Share.t) (t: type) :=
  (!! (legal_alignas_type t = true)) && (!! (nested_legal_fieldlist t = true)) &&
  (fun (_:reptype t) p => (!! (size_compatible t p /\ align_compatible t p))) 
  && data_at' sh empty_ti t 0.

Definition data_at_ (sh: Share.t) (t: type) := data_at sh t (default_val _).
*)

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

local_facts, isptr and offset_zero properties of array_at', data_at', data_at
and data_at_.

************************************************)
(*
(* not true now *)
Lemma array_at'_local_facts: forall t lo hi P v p,
  array_at' t lo hi P v p |-- !! (isptr p).
Proof.
  intros.
  unfold array_at'.
  unfold at_offset.
  normalize.
Qed.
*)
(*
Lemma data_at'_local_facts:
  forall sh t v p, data_at' sh t v p |-- !!(isptr p).
Proof.
  intros.
  revert p.
  apply (type_mut (fun (t: type) => forall pos v p, (data_at' sh e t pos v p |-- !!(isptr p))) (fun _ => True) (fun flds => (forall alignment pos v p, sfieldlist_at' sh e flds alignment pos v p |-- !!(isptr p)) /\ (forall alignment pos v p, ufieldlist_at' sh e flds alignment pos v p |-- !!(isptr p)))); intros; auto; simpl; 
  try (unfold at_offset2; apply (@at_offset_preserve_local_facts val); intros; apply mapsto_local_facts);
  try (unfold at_offset2; apply (@at_offset_preserve_local_facts val); intros; apply memory_block_local_facts).
  + apply array_at'_local_facts.
  + destruct H. apply H. (* struct case *)
  + destruct H. apply H0. (* union case *)
  + split; intros. (* Fnil case of fieldlist induction *)
    - normalize.
    - destruct (Zeq_bool alignment 0); normalize.
  + destruct H0. split; intros.
    - destruct (is_Fnil f).
      * apply withspacer_preserve_local_facts; intros. apply H.
      * eapply (derives_left_sepcon_right_corable (!!isptr p) _); [apply corable_prop|].
        apply withspacer_preserve_local_facts; intros. apply H.
    - destruct (is_Fnil f).
      * apply withspacer_preserve_local_facts; intros. apply H.
      * destruct v0; [apply withspacer_preserve_local_facts; intros; apply H | apply H1].
Qed.
Lemma array_at'_isptr: forall sh t lo hi P pos v p,
  array_at' sh t lo hi P pos v p = !! (isptr p) && array_at' sh t lo hi P pos v p.
Proof. intros. rewrite <- local_facts_isptr. reflexivity. apply array_at'_local_facts. Qed.

Lemma array_at'_offset_zero: forall sh t lo hi P pos v p,
  array_at' sh t lo hi P pos v p = array_at' sh t lo hi P pos v (offset_val Int.zero p).
Proof. intros. rewrite <- local_facts_offset_zero. reflexivity. apply array_at'_local_facts. Qed.

Lemma data_at'_isptr:
  forall sh e t pos v p, data_at' sh e t pos v p = !!(isptr p) && data_at' sh e t pos v p.
Proof. intros. rewrite <- local_facts_isptr. reflexivity. apply data_at'_local_facts. Qed.

Lemma data_at'_offset_zero:
  forall sh e t pos v p, data_at' sh e t pos v p = data_at' sh e t pos v (offset_val Int.zero p).
Proof. intros. rewrite <- local_facts_offset_zero. reflexivity. apply data_at'_local_facts. Qed.
*)

(*
Lemma data_at_local_facts: forall sh t v p, data_at sh t v p |-- !!(isptr p).
Proof. intros. unfold data_at. simpl. apply andp_left2. apply data_at'_local_facts. Qed.
Hint Resolve data_at_local_facts : saturate_local.

Lemma data_at_isptr: forall sh t v p, data_at sh t v p = !!(isptr p) && data_at sh t v p.
Proof. intros.
 apply pred_ext; normalize.
 apply andp_right; auto.
 unfold data_at. simpl.
 rewrite data_at'_isptr;  normalize.
Qed.

Lemma data_at_offset_zero: forall sh t v p, data_at sh t v p = data_at sh t v (offset_val Int.zero p).
Proof. intros. rewrite <- local_facts_offset_zero. reflexivity.
    intros; rewrite data_at_isptr; normalize.  
Qed.

Lemma data_at__isptr: forall sh t p, data_at_ sh t p = !!(isptr p) && data_at_ sh t p.
Proof. intros. unfold data_at_. apply data_at_isptr. Qed.

Lemma data_at__offset_zero: forall sh t p, data_at_ sh t p = data_at_ sh t (offset_val Int.zero p).
Proof. intros. unfold data_at_. apply data_at_offset_zero. Qed.

Hint Rewrite <- data_at__offset_zero: norm.
Hint Rewrite <- data_at_offset_zero: norm.
Hint Rewrite <- data_at__offset_zero: cancel.
Hint Rewrite <- data_at_offset_zero: cancel.
*)
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
  data_at' sh t (default_val t) p = memory_block sh (Int.repr (sizeof cenv_cs t)) p.
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
  apply memory_block_mapsto_; auto.
  + destruct i; auto.
  + destruct f; auto.
Qed.

Lemma by_value_data_at'_default_val2: forall sh t b ofs,
  type_is_by_value t = true ->
  legal_alignas_type t = true ->
  0 <= ofs /\ ofs + sizeof cenv_cs t <= Int.modulus ->
  (alignof cenv_cs t | ofs) ->
  data_at' sh t (default_val t) (Vptr b (Int.repr ofs)) =
  memory_block sh (Int.repr (sizeof cenv_cs t)) (Vptr b (Int.repr ofs)).
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
    [ rewrite <- legal_alignas_type_Tarray with (a0 := a) (z0 := z) by auto; auto
    | apply Z.divide_mul_l;
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

Lemma memory_block_data_at'_default_val: forall sh t b ofs
  (LEGAL_ALIGNAS: legal_alignas_type t = true)
  (LEGAL_COSU: legal_cosu_type t = true)
  (COMPLETE: complete_type cenv_cs t = true),
  0 <= ofs /\ ofs + sizeof cenv_cs t <= Int.modulus ->
  sizeof cenv_cs t < Int.modulus -> (* check why need this *)
  (alignof cenv_cs t | ofs) ->
  data_at' sh t (default_val t) (Vptr b (Int.repr ofs)) =
    memory_block sh (Int.repr (sizeof cenv_cs t)) (Vptr b (Int.repr ofs)).
Proof.
  intros sh t.
  type_induction t; intros;
  try solve [inversion COMPLETE];
  try solve [apply by_value_data_at'_default_val2; auto];
  rewrite data_at'_ind.
  + rewrite (default_val_ind (Tarray t z a)).
    rewrite unfold_fold_reptype.
    rewrite array_pred_ext with
     (P1 := fun i _ p => memory_block sh (Int.repr (sizeof cenv_cs t))
                          (offset_val (Int.repr (sizeof cenv_cs t * i)) p))
     (v1 := nil).
    Focus 2. {
      intros.
      rewrite Znth_nil.
      rewrite at_offset_eq3.
      unfold offset_val.
      solve_mod_modulus.
      simpl sizeof in H, H0;
      rewrite Z.max_r in H, H0 by omega.
      apply IH; try AUTO_IND;
      pose_size_mult cenv_cs t (0 :: i :: i + 1 :: z :: nil); omega.
    } Unfocus.
    apply memory_block_array_pred; [simpl in H; auto | auto].
  + rewrite default_val_ind.
    rewrite unfold_fold_reptype.
    rewrite struct_pred_ext with
     (P1 := fun it _ p =>
              memory_block sh (Int.repr 
               (field_offset_next cenv_cs (fst it) (co_members (get_co id)) (co_sizeof (get_co id)) -
                  field_offset cenv_cs (fst it) (co_members (get_co id))))
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
      rewrite proj_struct_gen by auto.
      rewrite Forall_forall in IH.
      specialize (IH (i, field_type i (co_members (get_co id)))).
      spec IH; [apply in_members_field_type; auto |].
      unfold snd in IH.
      rewrite IH by (try AUTO_IND; try (pose_field; omega)).
      rewrite Z.add_assoc, sepcon_comm, <- memory_block_split by (pose_field; omega).
      f_equal; f_equal; omega.
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
       (P1 := fun it _ =>
                memory_block sh (Int.repr (co_sizeof (get_co id))))
       (v1 := (union_default_val (co_members (get_co id))));
      [| apply get_co_members_no_replicate | reflexivity |].
      * rewrite memory_block_union_pred by (apply get_co_members_nil_sizeof_0).
        rewrite sizeof_Tunion.
        auto.
      * intros.
        pose proof get_co_members_no_replicate id as NO_REPLI.
        assert (in_members i (co_members (get_co id)))
          by (rewrite H3; apply members_union_inj_in_members; auto).
        rewrite withspacer_spacer.
        simpl.
        rewrite spacer_memory_block by (simpl; auto).
        unfold offset_val; solve_mod_modulus.
        unfold union_default_val.
        rewrite proj_union_gen by auto.
        rewrite Forall_forall in IH.
        specialize (IH (i, field_type i (co_members (get_co id)))).
        spec IH; [apply in_members_field_type; auto |].
        unfold snd in IH.
        rewrite IH; (try AUTO_IND; try (pose_field; omega)).
        rewrite sepcon_comm, <- memory_block_split by (pose_field; omega).
        f_equal; f_equal; omega.
Qed.

(*
Lemma data_at__memory_block: forall (sh : share) (t : type) (p: val),
  nested_non_volatile_type t = true ->
  sizeof t < Int.modulus ->
  data_at_ sh t p =
  !! (legal_alignas_type t = true) &&
  !! (nested_legal_fieldlist t = true) &&
  !! (align_compatible t p) && memory_block sh (Int.repr (sizeof t)) p.
Proof.
  intros.
  simpl.
  destruct p;
    try (rewrite memory_block_isptr;
     rewrite data_at__isptr;
     apply pred_ext; normalize; reflexivity).
  unfold data_at_, data_at.
  simpl.
  rewrite memory_block_size_compatible by auto.
  unfold size_compatible.
  cut (legal_alignas_type t = true ->
       Int.unsigned i + sizeof t <= Int.modulus ->
      (alignof t | Int.unsigned i) -> 
       data_at' sh empty_ti t 0 (default_val t) (Vptr b i) =
       memory_block sh (Int.repr (sizeof t)) (Vptr b i)).
  Focus 1. {
    intros; apply pred_ext; normalize.
    + rewrite H1 by auto.
      cancel.
    + rewrite H1 by auto.
      cancel.
  } Unfocus.
  intros.
  rewrite memory_block_offset_zero.
  apply memory_block_data_at'_default_val; auto.
  + omega.
  + apply Z.divide_0_r.
Qed.

Lemma memory_block_data_at_:
  forall (sh : share) (t : type) (p : val),
  legal_alignas_type t = true ->
  nested_legal_fieldlist t = true ->
  nested_non_volatile_type t = true ->
  align_compatible t p ->
  sizeof t < Int.modulus ->
  memory_block sh (Int.repr (sizeof t)) p = data_at_ sh t p.
Proof.
  intros.
  rewrite data_at__memory_block by eauto.
  normalize.
Qed.

Lemma data_at__memory_block_cancel:
   forall sh t p sz, 
       nested_non_volatile_type t = true ->
       sizeof t <= Int.max_unsigned ->
       sz = Int.repr (sizeof t) ->
       data_at_ sh t p |-- memory_block sh sz p.
Proof.
intros.
 subst.
 rewrite data_at__memory_block; auto.
 apply andp_left2. auto.
 change (Int.modulus) with (Int.max_unsigned + 1).
 omega.
Qed.

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

Lemma data_at_non_volatile: forall sh t v p, 
  data_at sh t v p |-- !! (nested_non_volatile_type t = true).
Proof.
  admit.
Qed.
*)
(*
Lemma array_at'_array_at'_: forall sh t lo hi P v pos p,
  lo < hi ->
  (legal_alignas_type t = true) ->
  (alignof t | pos) ->
  (forall n : Z,
       lo <= n < hi ->
       forall v p,
       P (pos + sizeof t * n) v p
       |-- P (pos + sizeof t * n) (default_val t) p) ->
  array_at' sh t lo hi P pos v p |-- array_at' sh t lo hi P pos nil p.
Proof.
  intros.
  unfold array_at'.
  unfold rangespec.
  assert (lo <= hi) by omega; clear H.
  apply andp_derives; [apply derives_refl |].
  remember (nat_of_Z (hi - lo)) as n eqn:HH; revert lo v H3 H2 HH; induction n; intros.
  + simpl.
    apply derives_refl.
  + simpl.
    assert (nat_of_Z (hi - lo) >= 1)%nat by omega.
    destruct (zlt 0 (hi - lo)); [| rewrite nat_of_Z_neg in H; omega].
    apply sepcon_derives.
    - unfold Znth. if_tac; [omega | rewrite Z.sub_diag].
      simpl.
      apply H2.
      omega.
    - erewrite rangespec'_ext.
      Focus 2. {
        intros.
        rewrite Znth_succ by omega.
        instantiate (1 := fun i => P (pos + sizeof t * i) (Znth (i - Z.succ lo)
                     (skipn 1 v) (default_val t))).
        reflexivity.
      } Unfocus.
      eapply derives_trans.
      Focus 1. {
        apply IHn; [omega | |].
        + intros. apply H2. omega.
        + rewrite (juicy_mem_lemmas.nat_of_Z_lem1 _ _ HH).
          f_equal; omega.
      } Unfocus.
      erewrite rangespec'_ext.
      Focus 2. {
        intros.
        change (@nil (reptype t)) with (skipn 1 (@nil (reptype t))).
        rewrite <- Znth_succ by omega.
        instantiate (1 := fun i => P (pos + sizeof t * i) (Znth (i - lo) nil (default_val t))).
        reflexivity.
      } Unfocus.
      apply derives_refl.
Qed.
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
  try solve [rewrite !data_at'_ind;
             if_tac; [auto | rewrite default_val_ind, unfold_fold_reptype; apply mapsto_mapsto_]].
  + rewrite !data_at'_ind.
    apply array_pred_ext_derives.
    intros.
    rewrite !at_offset_eq3.
    rewrite default_val_ind with (t0 := (Tarray t z a)), unfold_fold_reptype.
    rewrite Znth_nil.
    simpl sizeof in H, H0;
    rewrite Z.max_r in H, H0 by omega.
    apply IH; try AUTO_IND;
    pose_size_mult cenv_cs t (0 :: i :: i + 1 :: z :: nil); omega.
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
    rewrite proj_struct_gen by auto.
    apply IH; try AUTO_IND; try (pose_field; omega).
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
          (P1 := fun _ _ => memory_block sh (Int.repr (sizeof cenv_cs (Tunion id a))));
          [auto | reflexivity | ].
        intros.
        clear H4.
        assert (in_members i (co_members (get_co id))) by (subst; apply members_union_inj_in_members; auto).
        rewrite withspacer_spacer, sizeof_Tunion.
        simpl.
        pattern (co_sizeof (get_co id)) at 2;
        replace (co_sizeof (get_co id)) with (sizeof cenv_cs (field_type i (co_members (get_co id))) +
          (co_sizeof (get_co id) - sizeof cenv_cs (field_type i (co_members (get_co id))))) by omega.
        rewrite sepcon_comm.
        rewrite memory_block_split by (pose_field; omega).
        apply sepcon_derives; [| rewrite spacer_memory_block by (simpl; auto);
                                 unfold offset_val; solve_mod_modulus; auto ].
        rewrite <- memory_block_data_at'_default_val by (try AUTO_IND; try (pose_field; omega)).
        rewrite Forall_forall in IH.
        specialize (IH (i, (field_type i (co_members (get_co id))))).
        spec IH; [apply in_members_field_type; auto |].
        unfold snd in IH.
        apply IH; try AUTO_IND; try (pose_field; omega).
      * rewrite sizeof_Tunion.
        rewrite memory_block_union_pred by (apply get_co_members_nil_sizeof_0).
        auto.
Qed.

(*
Lemma data_at_data_at_ : forall sh t v p, 
  data_at sh t v p |-- data_at_ sh t p.
Proof.
  intros.
  destruct p;
    try (rewrite data_at_isptr;
     rewrite data_at__isptr;
     normalize; reflexivity).
  unfold data_at_, data_at.
  simpl.
  normalize.
  apply data_at'_data_at'_.
  + exact H1.
  + omega.
  + apply Z.divide_0_r.
  + exact H0.
Qed.

(* We do these as Hint Extern, instead of Hint Resolve,
  to limit their application and make them fail faster *)

Hint Extern 1 (data_at _ _ _ _ |-- data_at_ _ _ _) =>
    (apply data_at_data_at_) : cancel.

Lemma data_at_memory_block:
   forall sh t v p sz, 
       nested_non_volatile_type t = true ->
       sizeof t <= Int.max_unsigned ->
       sz = Int.repr (sizeof t) ->
       data_at sh t v p |-- memory_block sh sz p.
Proof.
intros.
 subst.
 eapply derives_trans; [apply data_at_data_at_; reflexivity |].
 rewrite data_at__memory_block; auto.
 apply andp_left2. auto.
 change (Int.modulus) with (Int.max_unsigned + 1).
 omega.
Qed.


Lemma f_equal_Int_repr:
  forall i j, i=j -> Int.repr i = Int.repr j.
Proof. intros; congruence. Qed.

Lemma sizeof_Tarray:
  forall t (n:Z) a, n >= 0 ->
      sizeof (Tarray t n a) = (sizeof t * n)%Z.
Proof.
intros; simpl. rewrite Z.max_r; omega.
Qed.

Hint Extern 1 (data_at_ _ _ _ |-- memory_block _ _ _) =>
    (simple apply data_at__memory_block_cancel;
       [reflexivity 
       | rewrite ?sizeof_Tarray by omega;
         rewrite ?sizeof_tuchar, ?Z.mul_1_l;simpl; 
         repable_signed 
       | try apply f_equal_Int_repr;
         rewrite ?sizeof_Tarray by omega;
         rewrite ?sizeof_tuchar, ?Z.mul_1_l; simpl; repable_signed
       ])
    : cancel.

Hint Extern 1 (data_at _ _ _ _ |-- memory_block _ _ _) =>
    (simple apply data_at_memory_block; 
       [reflexivity 
       | rewrite ?sizeof_Tarray by omega;
         rewrite ?sizeof_tuchar, ?Z.mul_1_l;simpl; 
         repable_signed 
       | try apply f_equal_Int_repr;
         rewrite ?sizeof_Tarray by omega;
         rewrite ?sizeof_tuchar, ?Z.mul_1_l; simpl; repable_signed
       ])
    : cancel.


Hint Extern 1 (data_at _ _ _ _ |-- memory_block _ _ _) =>
    (simple apply data_at_memory_block; [reflexivity | simpl; repable_signed | reflexivity])
    : cancel.


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

Lemma var_block_data_at_:
  forall  sh id t, 
  legal_alignas_type t = true ->
  nested_legal_fieldlist t = true ->
  nested_non_volatile_type t = true ->
  Z.ltb (sizeof t) Int.modulus = true ->
  var_block sh (id, t) = 
   !!(sizeof t <= Int.max_unsigned) &&
            `(data_at_ sh t) (eval_lvar id t).
Proof.
  intros; extensionality rho.
 unfold var_block.
  unfold_lift.
  simpl.
  apply Zlt_is_lt_bool in H2.
  rewrite data_at__memory_block by auto.
  rewrite memory_block_isptr.
  unfold local, lift1; unfold_lift.
  unfold align_compatible.
  destruct (eval_lvar id t rho); simpl in *; normalize.
  apply pred_ext; normalize.
Qed.

*)

End CENV.