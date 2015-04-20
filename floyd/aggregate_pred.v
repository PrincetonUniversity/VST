Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.type_induction.
Require Import floyd.fieldlist.
Require Import floyd.nested_field_lemmas.
Require Import floyd.mapsto_memory_block.
Require Export floyd.rangespec_lemmas.
Require Import floyd.reptype_lemmas.
Require Import floyd.jmeq_lemmas.
Require Import Coq.Logic.JMeq.

Open Scope logic.

(******************************************

Definition of at_offset.

at_offset is the elementary definition. All useful lemmas about at_offset' will be proved here. 

******************************************)

Definition at_offset (P: val -> mpred) (z: Z): val -> mpred :=
 fun v => P (offset_val (Int.repr z) v).

Arguments at_offset P z v : simpl never.

Lemma at_offset_eq: forall P z v,
  at_offset P z v = P (offset_val (Int.repr z) v).
Proof.
intros; auto.
Qed.

Lemma lifted_at_offset_eq: forall (P: val -> mpred) z v,
  `(at_offset P z) v = `P (`(offset_val (Int.repr z)) v).
Proof.
  intros.
  unfold liftx, lift in *. simpl in *.
  extensionality p.
  apply at_offset_eq.
Qed.

Lemma at_offset_eq2: forall pos pos' P, 
  forall p, at_offset P (pos + pos') p = at_offset P pos' (offset_val (Int.repr pos) p).
Proof.
  intros.
  rewrite at_offset_eq.
  rewrite at_offset_eq. 
  unfold offset_val.
  destruct p; auto.
  rewrite int_add_assoc1.
  reflexivity.
Qed.

Lemma at_offset_eq3: forall P z b ofs,
  at_offset P z (Vptr b (Int.repr ofs)) = P (Vptr b (Int.repr (ofs + z))).
Proof.
  intros.
  rewrite at_offset_eq.
  unfold offset_val.
  solve_mod_modulus.
  reflexivity.
Qed.

Lemma at_offset_derives: forall P Q p , (forall p, P p |-- Q p) -> forall pos, at_offset P pos p |-- at_offset Q pos p.
Proof.
  intros.
  rewrite !at_offset_eq.
  apply H.
Qed.

(******************************************

Definition of aggregate predicates.

******************************************)

Section CENV.

Context {cs: compspecs}.

Definition array_pred (t: type) (lo hi: Z) (P: reptype t -> val -> mpred) (v: list (reptype t)) (p: val): mpred :=
  rangespec lo hi (fun i => at_offset (P (Znth (i - lo) v (default_val _))) (sizeof cenv_cs t * i)) p.

Definition struct_pred (m: members) {A: ident * type -> Type} (P: forall it, A it -> val -> mpred) (v: compact_prod (map A m)): val -> mpred.
Proof.
  destruct m as [| (i0, t0) m]; [exact (fun _ => emp) |].
  revert i0 t0 v; induction m as [| (i0, t0) m]; intros ? ? v.
  + simpl in v.
    exact (P _ v).
  + simpl in v.
    exact ((P _ (fst v)) * IHm i0 t0 (snd v)).
Defined.

(* when unfold, do cbv [struct_pred list_rect]. *)

Definition union_pred (m: members) {A: ident * type -> Type} (P: forall it, A it -> val -> mpred) (v: compact_sum (map A m)): val -> mpred.
Proof.
  destruct m as [| (i0, t0) m]; [exact (fun _ => emp) |].
  revert i0 t0 v; induction m as [| (i0, t0) m]; intros ? ? v.
  + simpl in v.
    exact (P _ v).
  + simpl in v.
    destruct v as [v | v].
    - exact (P _ v).
    - exact (IHm i0 t0 v).
Defined.

(******************************************

Properties

******************************************)

Lemma array_pred_ext_derives: forall t lo hi P0 P1 v0 v1 p,
  (forall i, lo <= i < hi ->
     at_offset (P0 (Znth (i - lo) v0 (default_val t))) (sizeof cenv_cs t * i) p |--
     at_offset (P1 (Znth (i - lo) v1 (default_val t))) (sizeof cenv_cs t * i) p) ->
  array_pred t lo hi P0 v0 p |-- array_pred t lo hi P1 v1 p.
Proof.
  intros.
  unfold array_pred.
  unfold rangespec.
  apply rangespec_ext_derives; auto.
Qed.

Lemma array_pred_ext: forall t lo hi P0 P1 v0 v1 p,
  (forall i, lo <= i < hi ->
     at_offset (P0 (Znth (i - lo) v0 (default_val t))) (sizeof cenv_cs t * i) p =
     at_offset (P1 (Znth (i - lo) v1 (default_val t))) (sizeof cenv_cs t * i) p) ->
  array_pred t lo hi P0 v0 p = array_pred t lo hi P1 v1 p.
Proof.
  intros.
  unfold array_pred.
  unfold rangespec.
  apply rangespec_ext; auto.
Qed.

Lemma memory_block_array_pred: forall sh t b ofs lo hi,
  0 <= ofs + sizeof cenv_cs t * lo /\ ofs + sizeof cenv_cs t * hi <= Int.modulus ->
  0 <= lo <= hi ->
  sizeof cenv_cs t * (hi - lo) < Int.modulus ->
  array_pred t lo hi
    (fun _ : reptype t => memory_block sh (Int.repr (sizeof cenv_cs t))) nil
    (Vptr b (Int.repr ofs)) =
  memory_block sh (Int.repr (sizeof cenv_cs t * (hi - lo))) (Vptr b (Int.repr (ofs + sizeof cenv_cs t * lo))).
Proof.
  intros.
  unfold array_pred.
  unfold rangespec.
  remember (nat_of_Z (hi - lo)) as n eqn:HH; revert lo HH H H0 H1; induction n; intros.
  + simpl.
    pose proof arith_aux00 _ _ (proj2 H0) HH.
    rewrite H2, Z.mul_0_r, memory_block_zero_Vptr.
    reflexivity.
  + simpl.
    pose proof arith_aux01 _ _ _ HH.
    rewrite at_offset_eq3.
    pose_size_mult cenv_cs t (0 :: hi - Z.succ lo :: hi - lo :: nil).
    rewrite IHn; [| apply arith_aux02; auto | omega | omega | omega].
    replace (ofs + sizeof cenv_cs t * Z.succ lo) with (ofs + sizeof cenv_cs t * lo + sizeof cenv_cs t) by omega.
    rewrite <- memory_block_split by (auto; omega).
    f_equal.
    f_equal.
    omega.
Qed.

Definition proj_struct (i : ident) (m : members) {A: ident * type -> Type} (v: compact_prod (map A m)) (d: A (i, field_type2 i m)): A (i, field_type2 i m).
Proof.
  destruct m as [| (i0, t0) m]; [exact d |].
  unfold field_type2 in *.
  revert i0 t0 v d; induction m as [| (i1, t1) m]; intros.
  + simpl in *.
    if_tac.
    - subst; exact v.
    - exact d.
  + change (field_type i ((i0, t0) :: (i1, t1) :: m)) with
      (if ident_eq i i0 then Errors.OK t0 else field_type i ((i1, t1) :: m)) in *.
    if_tac.
    - subst; exact (fst v).
    - exact (IHm i1 t1 (snd v) d).
Defined.

Definition proj_union (i : ident) (m : members) {A: ident * type -> Type} (v: compact_sum (map A m)) (d: A (i, field_type2 i m)): A (i, field_type2 i m).
Proof.
  destruct m as [| (i0, t0) m]; [exact d |].
  unfold field_type2 in *.
  revert i0 t0 v d; induction m as [| (i1, t1) m]; intros.
  + simpl in *.
    if_tac.
    - subst; exact v.
    - exact d.
  + change (field_type i ((i0, t0) :: (i1, t1) :: m)) with
      (if ident_eq i i0 then Errors.OK t0 else field_type i ((i1, t1) :: m)) in *.
    if_tac.
    - subst; destruct v as [v | v].
      * exact v.
      * exact d.
    - destruct v as [v | v].
      * exact d.
      * exact (IHm i1 t1 v d).
Defined.

Lemma struct_pred_ext_derives: forall m {A0 A1} (P0: forall it, A0 it -> val -> mpred) (P1: forall it, A1 it -> val -> mpred) v0 v1 p,
  members_no_replicate m = true ->
  (forall i d0 d1, in_members i m ->
     P0 _ (proj_struct i m v0 d0) p |-- P1 _ (proj_struct i m v1 d1) p) ->
  struct_pred m P0 v0 p |-- struct_pred m P1 v1 p.
Proof.
  unfold field_type2.
  intros.
  destruct m as [| (i0, t0) m]; [simpl; auto |].
  revert i0 t0 v0 v1 H H0; induction m as [| (i1, t1) m]; intros.
  + specialize (H0 i0).
    simpl in H0.
    if_tac in H0; [| congruence].
    specialize (H0 v0 v1).
    spec H0; [left; reflexivity |].
    unfold eq_rect_r in H0; rewrite <- !eq_rect_eq in H0.
    simpl.
    exact H0.
  + change (struct_pred ((i0, t0) :: (i1, t1) :: m) P0 v0 p) with
      (P0 (i0, t0) (fst v0) p * struct_pred ((i1, t1) :: m) P0 (snd v0) p).
    change (struct_pred ((i0, t0) :: (i1, t1) :: m) P1 v1 p) with
      (P1 (i0, t0) (fst v1) p * struct_pred ((i1, t1) :: m) P1 (snd v1) p).
    apply sepcon_derives.
    - specialize (H0 i0).
      simpl in H0.
      if_tac in H0; [| congruence].
      specialize (H0 (fst v0) (fst v1)).
      spec H0; [left; reflexivity |].
      unfold eq_rect_r in H0; rewrite <- !eq_rect_eq in H0.
      simpl.
      exact H0.
    - rewrite members_no_replicate_ind in H.
      apply IHm; [tauto |].
      intros.
      specialize (H0 i).
      simpl in H0.
      if_tac in H0.
      * clear - H H1 H2.
        subst.
        tauto.
      * specialize (H0 d0 d1).
        spec H0; [right; auto |].
        exact H0.
Qed.

Lemma struct_pred_ext: forall m {A0 A1} (P0: forall it, A0 it -> val -> mpred) (P1: forall it, A1 it -> val -> mpred) v0 v1 p,
  members_no_replicate m = true ->
  (forall i d0 d1, in_members i m ->
     P0 _ (proj_struct i m v0 d0) p = P1 _ (proj_struct i m v1 d1) p) ->
  struct_pred m P0 v0 p = struct_pred m P1 v1 p.
Proof.
  intros.
  apply pred_ext; eapply struct_pred_ext_derives; eauto;
  intros; erewrite H0 by eauto; auto.
Qed.

Lemma memory_block_struct_pred: forall sh m sz {A} (v: compact_prod (map A m)) b ofs,
  (m = nil -> sz = 0) ->
  members_no_replicate m = true ->
  sizeof_struct cenv_cs 0 m <= sz < Int.modulus ->
  0 <= ofs /\ ofs + sz <= Int.modulus ->
  struct_pred m
   (fun it _ =>
      at_offset
        (memory_block sh (Int.repr (field_offset_next cenv_cs (fst it) m sz -
                                    field_offset2 cenv_cs (fst it) m)))
        (field_offset2 cenv_cs (fst it) m)) v (Vptr b (Int.repr ofs)) =
  memory_block sh (Int.repr sz) (Vptr b (Int.repr ofs)).
Proof.
  unfold field_offset2, field_offset, field_offset_next.
  intros sh m sz A v b ofs NIL_CASE NO_REPLI; intros.
  destruct m as [| (i0, t0) m].
  1: rewrite (NIL_CASE eq_refl), memory_block_zero; simpl; normalize.
  assert (align 0 (alignof cenv_cs t0) = 0) by apply align_0, alignof_pos.
  revert H0; pattern ofs at 1 4; replace ofs with (ofs + align 0 (alignof cenv_cs t0)) by omega; intros.
  revert H; pattern sz at 2 4; replace sz with (sz - align 0 (alignof cenv_cs t0)) by omega; intros.
  pattern 0 at 1; rewrite <- H1.
  clear NIL_CASE H1.
  revert H H0; generalize 0 at 1 2 4 5 6 8 10 11; revert i0 t0 v NO_REPLI;
  induction m as [| (i1, t1) m]; intros.
  + simpl.
    if_tac; [| congruence].
    apply at_offset_eq3.
  + match goal with
    | |- struct_pred ((i0, t0) :: (i1, t1) :: m) ?P v ?p = _ =>
           change (struct_pred ((i0, t0) :: (i1, t1) :: m) P v p) with
             (P (i0, t0) (fst v) p * struct_pred ((i1, t1) :: m) P (snd v) p);
           simpl (P (i0, t0) (fst v) p)
    end.
    if_tac; [| congruence].
    rewrite at_offset_eq3.
    erewrite struct_pred_ext.
    - rewrite members_no_replicate_ind in NO_REPLI; destruct NO_REPLI as [NOT_IN NO_REPLI].
      rewrite IHm with (z := align z (alignof cenv_cs t0) + sizeof cenv_cs t0);
        [| auto
         | simpl in H |- *; pose_align_le; pose_sizeof_pos; omega 
         | pose_align_le; pose_sizeof_pos; omega].
      replace (ofs + align (align z (alignof cenv_cs t0) + sizeof cenv_cs t0) (alignof cenv_cs t1)) with
        (ofs + align z (alignof cenv_cs t0) +
         (align (align z (alignof cenv_cs t0) + sizeof cenv_cs t0) (alignof cenv_cs t1) -
          align z (alignof cenv_cs t0))) by omega.
      rewrite <- memory_block_split by
        (simpl in H; revert H; pose_align_le; pose_sizeof_pos; intros; omega).
      f_equal; f_equal; omega.
    - rewrite members_no_replicate_ind in NO_REPLI; destruct NO_REPLI as [NOT_IN NO_REPLI].
      auto.
    - intros. instantiate (1 := (snd v)).
      rewrite !at_offset_eq3.
      unfold fst.
      pose proof im_members_tail_no_replicate _ _ _ _ NO_REPLI H2.
      rewrite (neq_field_offset_rec_cons cenv_cs i i0 t0) by auto.
      rewrite (neq_field_offset_next_rec_cons cenv_cs i i0 t0) by auto.
      reflexivity.
Qed.   

Definition members_union_inj {m: members} {A} (v: compact_sum (map A m)) : ident * type.
Proof.
  destruct m as [| (i0, t0) m]; [exact (1%positive, Tvoid) |].
  revert i0 t0 v; induction m as [| (i1, t1) m]; intros.
  + exact (i0, t0).
  + destruct v.
    - exact (i0, t0).
    - exact (IHm i1 t1 c).
Defined.

Lemma members_union_inj_in_members: forall m A (v: compact_sum (map A m)),
  m <> nil ->
  in_members (fst (members_union_inj v)) m.
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [congruence |].
  clear H.
  revert i0 t0 v; induction m as [| (i1, t1) m]; intros.
  + simpl.
    left; simpl.
    auto.
  + destruct v.
    - simpl.
      left; simpl.
      auto.
    - right.
      apply IHm.
Qed.

Lemma members_unions_inj_eq_spec: forall i0 t0 i1 t1 m A0 A1 (v0: compact_sum (map A0 ((i0, t0) :: (i1, t1) :: m))) (v1: compact_sum (map A1 ((i0, t0) :: (i1, t1) :: m))),
  members_no_replicate ((i0, t0) :: (i1, t1) :: m) = true ->
  (members_union_inj v0 = members_union_inj v1 <->
  match v0, v1 with
  | inl _, inl _ => True
  | inr v0, inr v1 => members_union_inj (v0: compact_sum (map A0 ((i1, t1) :: m))) = members_union_inj (v1: compact_sum (map A1 ((i1, t1) :: m)))
  | _, _ => False
  end).
Proof.
  intros.
  destruct v0 as [v0 | v0];
  [ change (members_union_inj (inl v0: compact_sum (map A0 ((i0, t0) :: (i1, t1) :: m)))) with (i0, t0)
  | change (members_union_inj (inr v0: compact_sum (map A0 ((i0, t0) :: (i1, t1) :: m)))) with
     (members_union_inj (v0: compact_sum (map A0 ((i1, t1) :: m))))];
  (destruct v1 as [v1 | v1];
  [ change (members_union_inj (inl v1: compact_sum (map A1 ((i0, t0) :: (i1, t1) :: m)))) with (i0, t0)
  | change (members_union_inj (inr v1: compact_sum (map A1 ((i0, t0) :: (i1, t1) :: m)))) with
     (members_union_inj (v1: compact_sum (map A1 ((i1, t1) :: m))))]).
  + tauto.
  + pose proof members_union_inj_in_members ((i1, t1) :: m) A1 v1.
    spec H0; [congruence |].
    split; [intros | tauto].
    rewrite <- H1 in H0; unfold fst in H0.
    rewrite members_no_replicate_ind in H.
    tauto.
  + pose proof members_union_inj_in_members ((i1, t1) :: m) A0 v0.
    spec H0; [congruence |].
    split; [intros | tauto].
    rewrite H1 in H0; unfold fst in H0.
    rewrite members_no_replicate_ind in H.
    tauto.
  + tauto.
Qed.

Lemma union_pred_ext_derives: forall m {A0 A1} (d0: forall it, A0 it) (d1: forall it, A1 it) (P0: forall it, A0 it -> val -> mpred) (P1: forall it, A1 it -> val -> mpred) v0 v1 p,
  members_no_replicate m = true ->
  members_union_inj v0 = members_union_inj v1 ->
  (forall i, in_members i m ->
     P0 _ (proj_union i m v0 (d0 _)) p |-- P1 _ (proj_union i m v1 (d1 _)) p) ->
  union_pred m P0 v0 p |-- union_pred m P1 v1 p.
Proof.
  unfold field_type2.
  intros.
  destruct m as [| (i0, t0) m]; [simpl; auto |].
  revert i0 t0 v0 v1 H H0 H1; induction m as [| (i1, t1) m]; intros.
  + specialize (H1 i0).
    spec H1; [left; reflexivity |].
    simpl in H1.
    if_tac in H1; [| congruence].
    unfold eq_rect_r in H1; rewrite <- !eq_rect_eq in H1.
    simpl.
    exact H1.
  + rewrite members_unions_inj_eq_spec in H0 by auto.
    destruct v0 as [v0 | v0], v1 as [v1 | v1]; try solve [inversion H0].
    - specialize (H1 i0).
      spec H1; [left; reflexivity |].
      simpl in H1.
      if_tac in H1; [| congruence].
      unfold eq_rect_r in H1; rewrite <- !eq_rect_eq in H1.
      simpl.
      exact H1.
    - rewrite members_no_replicate_ind in H.
      apply IHm; [tauto | tauto |].
      intros.
      specialize (H1 i).
      spec H1; [right; auto |].
      simpl in H1.
      if_tac in H1.
      * clear - H H1 H2.
        subst.
        tauto.
      * exact H1.
Qed.

Lemma union_pred_ext: forall m {A0 A1} (d0: forall it, A0 it) (d1: forall it, A1 it) (P0: forall it, A0 it -> val -> mpred) (P1: forall it, A1 it -> val -> mpred) v0 v1 p,
  members_no_replicate m = true ->
  members_union_inj v0 = members_union_inj v1 ->
  (forall i, in_members i m ->
     P0 _ (proj_union i m v0 (d0 _)) p = P1 _ (proj_union i m v1 (d1 _)) p) ->
  union_pred m P0 v0 p = union_pred m P1 v1 p.
Proof.
  intros.
  apply pred_ext; eapply union_pred_ext_derives; eauto;
  intros; rewrite H1 by auto; auto.
Qed.

Lemma memory_block_union_pred: forall sh m sz {A} (v: compact_sum (map A m)) b ofs,
  (m = nil -> sz = 0) ->
  union_pred m (fun it _ => memory_block sh (Int.repr sz)) v (Vptr b (Int.repr ofs)) =
  memory_block sh (Int.repr sz) (Vptr b (Int.repr ofs)).
Proof.
  intros sh m sz A v b ofs NIL_CASE; intros.
  destruct m as [| (i0, t0) m].
  1: rewrite (NIL_CASE eq_refl), memory_block_zero; simpl; normalize.
  clear NIL_CASE.
  revert i0 t0 v; induction m as [| (i1, t1) m]; intros.
  + simpl; auto.
  + destruct v.
    - simpl; auto.
    - apply IHm.
Qed.

End CENV.

