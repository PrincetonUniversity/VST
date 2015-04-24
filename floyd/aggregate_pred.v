Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.type_induction.
Require Import floyd.fieldlist.
Require Import floyd.compact_prod_sum.
Require Import floyd.mapsto_memory_block.
Require Import floyd.nested_pred_lemmas.
Require Import floyd.jmeq_lemmas.
Require Import Coq.Logic.JMeq.

Open Scope Z.
Open Scope logic.

(******************************************

Definition and lemmas about rangespec

******************************************)

Fixpoint rangespec (lo: Z) (n: nat) (P: Z -> val -> mpred): val -> mpred :=
  match n with
  | O => fun _ => emp
  | S n' => P lo * rangespec (Zsucc lo) n' P
 end.

Fixpoint fold_range' {A: Type} (f: Z -> A -> A) (zero: A) (lo: Z) (n: nat) : A :=
 match n with
  | O => zero
  | S n' => f lo (fold_range' f  zero (Zsucc lo) n')
 end.

Definition fold_range {A: Type} (f: Z -> A -> A) (zero: A) (lo hi: Z) : A :=
  fold_range' f zero lo (nat_of_Z (hi-lo)).

Lemma rangespec_shift_derives: forall lo lo' len P P' p p',
  (forall i i', lo <= i < lo + Z_of_nat len -> i - lo = i' - lo' -> P i p |-- P' i' p') -> 
  rangespec lo len P p |-- rangespec lo' len P' p'.
Proof.
  intros.
  revert lo lo' H; 
  induction len; intros.
  + simpl. auto.
  + simpl.
    apply sepcon_derives.
    - apply H; [| omega].
      rewrite Nat2Z.inj_succ.
      rewrite <- Z.add_1_r.
      omega.
    - apply IHlen. intros.
      apply H; [| omega].
      rewrite Nat2Z.inj_succ.
      rewrite <- Z.add_1_r.
      pose proof Zle_0_nat (S len).
      omega.
Qed.

Lemma rangespec_ext_derives: forall lo len P P' p,
  (forall i, lo <= i < lo + Z_of_nat len -> P i p |-- P' i p) -> 
  rangespec lo len P p |-- rangespec lo len P' p.
Proof.
  intros.
  apply rangespec_shift_derives.
  intros.
  assert (i = i') by omega.
  subst.
  apply H.
  auto.
Qed.

Lemma rangespec_shift: forall lo lo' len P P' p p',
  (forall i i', lo <= i < lo + Z_of_nat len -> i - lo = i' - lo' -> P i p = P' i' p') -> 
  rangespec lo len P p = rangespec lo' len P' p'.
Proof.
  intros; apply pred_ext; apply rangespec_shift_derives;
  intros.
  + erewrite H; eauto.
  + erewrite H; eauto.
    omega.
Qed.

Lemma rangespec_ext: forall lo len P P' p,
  (forall i, lo <= i < lo + Z_of_nat len -> P i p = P' i p) -> 
  rangespec lo len P p = rangespec lo len P' p.
Proof.
  intros; apply pred_ext; apply rangespec_ext_derives;
  intros; rewrite H; auto.
Qed.

Lemma rangespec_elim: forall lo len P i,
  lo <= i < lo + Z_of_nat len -> rangespec lo len P |-- P i * TT.
Proof.
  intros. revert lo i H; induction len; intros.
  + simpl in H. omega.
  + simpl. intros; destruct (Z.eq_dec i lo).
    - subst. cancel.
    - replace (P i x * !!True) with (TT * (P i x * TT)) by (apply pred_ext; cancel).
      apply sepcon_derives; [cancel |].
      apply IHlen.
      rewrite Nat2Z.inj_succ in H.
      rewrite <- Z.add_1_l in *.
      omega.
Qed.

(******************************************

Definition of aggregate predicates.

******************************************)

Definition array_pred {A: Type} (lo hi: Z) (d: A) (P: Z -> A -> val -> mpred) (v: list A): val -> mpred :=
  rangespec lo (nat_of_Z (hi-lo)) (fun i => P i (Znth (i - lo) v d)).

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

Lemma array_pred_ext_derives: forall A lo hi (d: A) P0 P1 v0 v1 p,
  (forall i, lo <= i < hi -> P0 i (Znth (i - lo) v0 d) p |-- P1 i (Znth (i - lo) v1 d) p) -> 
  array_pred lo hi d P0 v0 p |-- array_pred lo hi d P1 v1 p.
Proof.
  intros.
  unfold array_pred.
  apply rangespec_ext_derives.
  intros.
  destruct (zlt lo hi).
  + apply H.
    rewrite nat_of_Z_max in H0.
    rewrite Z.max_l in H0 by omega.
    omega.
  + rewrite nat_of_Z_max in H0.
    rewrite Z.max_r in H0 by omega.
    omega.
Qed.

Lemma array_pred_ext: forall A lo hi (d: A) P0 P1 v0 v1 p,
  (forall i, lo <= i < hi -> P0 i (Znth (i - lo) v0 d) p = P1 i (Znth (i - lo) v1 d) p) -> 
  array_pred lo hi d P0 v0 p = array_pred lo hi d P1 v1 p.
Proof.
  intros; apply pred_ext; apply array_pred_ext_derives;
  intros; rewrite H; auto.
Qed.

Lemma at_offset_array_pred: forall lo hi A P d (v: list A) ofs p,
  at_offset (array_pred lo hi d P v) ofs p = array_pred lo hi d (fun i v => at_offset (P i v) ofs) v p.
Proof.
  intros.
  rewrite at_offset_eq.
  unfold array_pred.
  apply rangespec_shift.
  intros.
  assert (i = i') by omega; subst i'; clear H0.
  rewrite at_offset_eq.
  auto.
Qed.

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

Lemma at_offset_struct_pred: forall m {A} (P: forall it, A it -> val -> mpred) v p ofs,
  at_offset (struct_pred m P v) ofs p = struct_pred m (fun it v => at_offset (P it v) ofs) v p.
Proof.
  intros.
  rewrite at_offset_eq.
  destruct m as [| (i0, t0) m]; [simpl; auto |].
  revert i0 t0 v; induction m as [| (i1, t1) m]; intros.
  + simpl.
    rewrite at_offset_eq.
    auto.
  + simpl.
    rewrite at_offset_eq.
    f_equal.
    apply IHm.
Qed.

Lemma union_pred_ext_derives: forall m {A0 A1} (P0: forall it, A0 it -> val -> mpred) (P1: forall it, A1 it -> val -> mpred) v0 v1 p,
  members_no_replicate m = true ->
  members_union_inj v0 = members_union_inj v1 ->
  (forall i d0 d1, i = fst (members_union_inj v0) -> i = fst (members_union_inj v1) ->
     P0 _ (proj_union i m v0 d0) p |-- P1 _ (proj_union i m v1 d1) p) ->
  union_pred m P0 v0 p |-- union_pred m P1 v1 p.
Proof.
  unfold field_type2.
  intros.
  destruct m as [| (i0, t0) m]; [simpl; auto |].
  revert i0 t0 v0 v1 H H0 H1; induction m as [| (i1, t1) m]; intros.
  + specialize (H1 i0).
    simpl in H1.
    if_tac in H1; [| congruence].
    specialize (H1 v0 v1).
    spec H1; [reflexivity |].
    spec H1; [reflexivity |].
    unfold eq_rect_r in H1; rewrite <- !eq_rect_eq in H1.
    simpl.
    exact H1.
  + rewrite members_unions_inj_eq_spec in H0 by auto.
    destruct v0 as [v0 | v0], v1 as [v1 | v1]; try solve [inversion H0].
    - specialize (H1 i0).
      simpl in H1.
      if_tac in H1; [| congruence].
      specialize (H1 v0 v1).
      spec H1; [reflexivity |].
      spec H1; [reflexivity |].
      unfold eq_rect_r in H1; rewrite <- !eq_rect_eq in H1.
      simpl.
      exact H1.
    - rewrite members_no_replicate_ind in H.
      apply IHm; [tauto | tauto |].
      intros.
      specialize (H1 i).
      simpl in H1.
      if_tac in H1.
      * clear - H H2 H4.
        pose proof members_union_inj_in_members _ _ v0.
        spec H0; [congruence |].
        subst.
        rewrite <- H2 in H0.
        tauto.
      * specialize (H1 d0 d1).
        spec H1; [auto |].
        spec H1; [auto |].
        exact H1.
Qed.

Lemma union_pred_ext: forall m {A0 A1} (P0: forall it, A0 it -> val -> mpred) (P1: forall it, A1 it -> val -> mpred) v0 v1 p,
  members_no_replicate m = true ->
  members_union_inj v0 = members_union_inj v1 ->
  (forall i d0 d1, i = fst (members_union_inj v0) -> i = fst (members_union_inj v1) ->
     P0 _ (proj_union i m v0 d0) p = P1 _ (proj_union i m v1 d1) p) ->
  union_pred m P0 v0 p = union_pred m P1 v1 p.
Proof.
  intros.
  apply pred_ext; eapply union_pred_ext_derives; eauto;
  intros; erewrite H1 by eauto; auto.
Qed.

Lemma at_offset_union_pred: forall m {A} (P: forall it, A it -> val -> mpred) v p ofs,
  at_offset (union_pred m P v) ofs p = union_pred m (fun it v => at_offset (P it v) ofs) v p.
Proof.
  intros.
  rewrite at_offset_eq.
  destruct m as [| (i0, t0) m]; [simpl; auto |].
  revert i0 t0 v; induction m as [| (i1, t1) m]; intros.
  + simpl.
    rewrite at_offset_eq.
    auto.
  + simpl.
    destruct v.
    - rewrite at_offset_eq.
      auto.
    - apply IHm.
Qed.

Section MEMORY_BLOCK_AGGREGATE.

Context {cs: compspecs}.

Lemma memory_block_array_pred: forall sh t A lo hi (d: A) v b ofs,
  0 <= ofs + sizeof cenv_cs t * lo /\ ofs + sizeof cenv_cs t * hi <= Int.modulus ->
  0 <= lo <= hi ->
  sizeof cenv_cs t * (hi - lo) < Int.modulus ->
  array_pred lo hi d
    (fun i _ p => memory_block sh (Int.repr (sizeof cenv_cs t))
                   (offset_val (Int.repr (sizeof cenv_cs t * i)) p)) v
    (Vptr b (Int.repr ofs)) =
  memory_block sh (Int.repr (sizeof cenv_cs t * (hi - lo))) (Vptr b (Int.repr (ofs + sizeof cenv_cs t * lo))).
Proof.
  intros.
  unfold array_pred.
  remember (nat_of_Z (hi - lo)) as n eqn:HH; revert lo HH H H0 H1; induction n; intros.
  + simpl.
    pose proof arith_aux00 _ _ (proj2 H0) HH.
    rewrite H2, Z.mul_0_r, memory_block_zero_Vptr.
    reflexivity.
  + simpl.
    pose proof arith_aux01 _ _ _ HH.
    solve_mod_modulus.
    pose_size_mult cenv_cs t (0 :: hi - Z.succ lo :: hi - lo :: nil).
    rewrite IHn; [| apply arith_aux02; auto | omega | omega | omega].
    replace (ofs + sizeof cenv_cs t * Z.succ lo) with (ofs + sizeof cenv_cs t * lo + sizeof cenv_cs t) by omega.
    rewrite <- memory_block_split by (auto; omega).
    f_equal.
    f_equal.
    omega.
Qed.

Lemma memory_block_array_pred': forall {A} sh t z (d: A) b ofs,
  0 <= ofs /\ ofs + sizeof cenv_cs t * Z.max 0 z <= Int.modulus ->
  sizeof cenv_cs t * Z.max 0 z < Int.modulus ->
  array_pred 0 z d
     (fun i _ p =>
      memory_block sh (Int.repr (sizeof cenv_cs t))
        (offset_val (Int.repr (sizeof cenv_cs t * i)) p)) nil
     (Vptr b (Int.repr ofs))  =
  memory_block sh (Int.repr (sizeof cenv_cs t * Z.max 0 z)) (Vptr b (Int.repr ofs)).
Proof.
  intros.
  destruct (zlt z 0).
  + unfold array_pred.
    simpl.
    rewrite Z2Nat_neg by omega.
    rewrite Z.max_l by omega.
    rewrite Z.mul_0_r.
    rewrite memory_block_zero.
    simpl; normalize.
  + rewrite memory_block_array_pred.
    - rewrite Z.mul_0_r, Z.sub_0_r, Z.add_0_r.
      f_equal; f_equal.
      simpl.
      f_equal.
      rewrite Z.max_r by omega; auto.
    - rewrite Z.mul_0_r, Z.add_0_r.
      simpl in H.
      rewrite Z.max_r in H by omega; auto.
    - omega.
    - rewrite Z.sub_0_r.
      simpl in H0.
      rewrite Z.max_r in H0 by omega; auto.
Qed.

Lemma memory_block_struct_pred: forall sh m sz {A} (v: compact_prod (map A m)) b ofs,
  (m = nil -> sz = 0) ->
  members_no_replicate m = true ->
  sizeof_struct cenv_cs 0 m <= sz < Int.modulus ->
  0 <= ofs /\ ofs + sz <= Int.modulus ->
  struct_pred m
   (fun it _ p =>
     (memory_block sh (Int.repr (field_offset_next cenv_cs (fst it) m sz - field_offset2 cenv_cs (fst it) m)))
     (offset_val (Int.repr (field_offset2 cenv_cs (fst it) m)) p)) v (Vptr b (Int.repr ofs)) =
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
    solve_mod_modulus.
    reflexivity.
  + match goal with
    | |- struct_pred ((i0, t0) :: (i1, t1) :: m) ?P v ?p = _ =>
           change (struct_pred ((i0, t0) :: (i1, t1) :: m) P v p) with
             (P (i0, t0) (fst v) p * struct_pred ((i1, t1) :: m) P (snd v) p);
           simpl (P (i0, t0) (fst v) p)
    end.
    if_tac; [| congruence].
    solve_mod_modulus.
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
      solve_mod_modulus.
      unfold fst.
      pose proof in_members_tail_no_replicate _ _ _ _ NO_REPLI H2.
      rewrite (neq_field_offset_rec_cons cenv_cs i i0 t0) by auto.
      rewrite (neq_field_offset_next_rec_cons cenv_cs i i0 t0) by auto.
      reflexivity.
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

End MEMORY_BLOCK_AGGREGATE.

Module aggregate_pred.

Export floyd.compact_prod_sum.compact_prod_sum.

Definition array_pred: forall {A: Type} (lo hi: Z) (d: A) (P: Z -> A -> val -> mpred) (v: list A), val -> mpred
:= @array_pred.

Definition struct_pred: forall (m: members) {A: ident * type -> Type} (P: forall it, A it -> val -> mpred) (v: compact_prod (map A m)), val -> mpred
:= @struct_pred.

Definition union_pred: forall (m: members) {A: ident * type -> Type} (P: forall it, A it -> val -> mpred) (v: compact_sum (map A m)), val -> mpred
:= @union_pred.

Definition array_pred_ext_derives:
  forall A lo hi (d: A) P0 P1 v0 v1 p,
  (forall i, lo <= i < hi -> P0 i (Znth (i - lo) v0 d) p |-- P1 i (Znth (i - lo) v1 d) p) -> 
  array_pred lo hi d P0 v0 p |-- array_pred lo hi d P1 v1 p
:= @array_pred_ext_derives.

Definition array_pred_ext:
  forall A lo hi (d: A) P0 P1 v0 v1 p,
  (forall i, lo <= i < hi -> P0 i (Znth (i - lo) v0 d) p = P1 i (Znth (i - lo) v1 d) p) -> 
  array_pred lo hi d P0 v0 p = array_pred lo hi d P1 v1 p
:= @array_pred_ext.

Definition at_offset_array_pred: forall lo hi A P d (v: list A) ofs p,
  at_offset (array_pred lo hi d P v) ofs p = array_pred lo hi d (fun i v => at_offset (P i v) ofs) v p
:= @at_offset_array_pred.

Definition struct_pred_ext_derives:
  forall m {A0 A1} (P0: forall it, A0 it -> val -> mpred) (P1: forall it, A1 it -> val -> mpred) v0 v1 p,
  members_no_replicate m = true ->
  (forall i d0 d1, in_members i m ->
     P0 _ (proj_struct i m v0 d0) p |-- P1 _ (proj_struct i m v1 d1) p) ->
  struct_pred m P0 v0 p |-- struct_pred m P1 v1 p
:= @struct_pred_ext_derives.

Definition struct_pred_ext:
  forall m {A0 A1} (P0: forall it, A0 it -> val -> mpred) (P1: forall it, A1 it -> val -> mpred) v0 v1 p,
  members_no_replicate m = true ->
  (forall i d0 d1, in_members i m ->
     P0 _ (proj_struct i m v0 d0) p = P1 _ (proj_struct i m v1 d1) p) ->
  struct_pred m P0 v0 p = struct_pred m P1 v1 p
:= @struct_pred_ext.

Definition at_offset_struct_pred: forall m {A} (P: forall it, A it -> val -> mpred) v p ofs,
  at_offset (struct_pred m P v) ofs p = struct_pred m (fun it v => at_offset (P it v) ofs) v p
:= @at_offset_struct_pred.

Definition union_pred_ext_derives:
  forall m {A0 A1} (P0: forall it, A0 it -> val -> mpred) (P1: forall it, A1 it -> val -> mpred) v0 v1 p,
  members_no_replicate m = true ->
  members_union_inj v0 = members_union_inj v1 ->
  (forall i d0 d1, i = fst (members_union_inj v0) -> i = fst (members_union_inj v1) ->
     P0 _ (proj_union i m v0 d0) p |-- P1 _ (proj_union i m v1 d1) p) ->
  union_pred m P0 v0 p |-- union_pred m P1 v1 p
:= @union_pred_ext_derives.

Definition union_pred_ext:
  forall m {A0 A1} (P0: forall it, A0 it -> val -> mpred) (P1: forall it, A1 it -> val -> mpred) v0 v1 p,
  members_no_replicate m = true ->
  members_union_inj v0 = members_union_inj v1 ->
  (forall i d0 d1, i = fst (members_union_inj v0) -> i = fst (members_union_inj v1) ->
     P0 _ (proj_union i m v0 d0) p = P1 _ (proj_union i m v1 d1) p) ->
  union_pred m P0 v0 p = union_pred m P1 v1 p
:= @union_pred_ext.

Definition at_offset_union_pred: forall m {A} (P: forall it, A it -> val -> mpred) v p ofs,
  at_offset (union_pred m P v) ofs p = union_pred m (fun it v => at_offset (P it v) ofs) v p
:= at_offset_union_pred.

End aggregate_pred.

Require Import floyd.reptype_lemmas.

(******************************************

Auxiliary predicates

******************************************)

Section AUXILIARY_PRED.

Context {cs: compspecs}.

Variable sh: share.

Definition struct_data_at'_aux (m m0: members) (sz: Z) (P: ListType (map (fun it => reptype (snd it) -> (val -> mpred)) m)) (v: compact_prod (map (fun it => reptype (snd it)) m)) : (val -> mpred).
Proof.
  destruct m as [| (i0, t0) m]; [exact (fun _ => emp) |].
  revert i0 t0 v P; induction m as [| (i0, t0) m]; intros ? ? v P.
  + simpl in v, P.
    inversion P; subst.
    exact (withspacer sh
            (field_offset2 cenv_cs i0 m0 + sizeof cenv_cs t0)
            (field_offset_next cenv_cs i0 m0 sz)
            (at_offset (a v) (field_offset2 cenv_cs i0 m0))).
  + simpl in v, P.
    inversion P; subst.
    exact (withspacer sh
            (field_offset2 cenv_cs i1 m0 + sizeof cenv_cs t1)
            (field_offset_next cenv_cs i1 m0 sz)
            (at_offset (a (fst v)) (field_offset2 cenv_cs i1 m0)) * IHm i0 t0 (snd v) b).
Defined.

Definition union_data_at'_aux (m: members) (sz: Z) (P: ListType (map (fun it => reptype (snd it) -> (val -> mpred)) m)) (v: compact_sum (map (fun it => reptype (snd it)) m)) : (val -> mpred).
Proof.
  destruct m as [| (i0, t0) m]; [exact (fun _ => emp) |].
  revert i0 t0 v P; induction m as [| (i0, t0) m]; intros ? ? v P.
  + simpl in v, P.
    inversion P; subst.
    exact (withspacer sh (sizeof cenv_cs t0) sz (a v)).
  + simpl in v, P.
    inversion P; subst.
    destruct v as [v | v].
    - exact (withspacer sh (sizeof cenv_cs t1) sz (a v)).
    - exact (IHm i0 t0 v b).
Defined.

Lemma struct_data_at'_aux_spec: forall m m0 sz v P,
  struct_data_at'_aux m m0 sz
   (ListTypeGen
     (fun it => reptype (snd it) -> val -> mpred)
     P m) v =
  struct_pred m 
   (fun it v =>
      withspacer sh
       (field_offset2 cenv_cs (fst it) m0 + sizeof cenv_cs (snd it))
       (field_offset_next cenv_cs (fst it) m0 sz)
       (at_offset (P it v) (field_offset2 cenv_cs (fst it) m0))) v.
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [reflexivity |].
  revert i0 t0 v; induction m as [| (i0, t0) m]; intros.
  + simpl; reflexivity.
  + change
     (struct_data_at'_aux ((i1, t1) :: (i0, t0) :: m) m0 sz
     (ListTypeGen (fun it : ident * type => reptype (snd it) -> val -> mpred)
        P ((i1, t1) :: (i0, t0) :: m)) v) with
     (withspacer sh
       (field_offset2 cenv_cs i1 m0 + sizeof cenv_cs t1)
         (field_offset_next cenv_cs i1 m0 sz)
           (at_offset (P (i1, t1) (fst v)) (field_offset2 cenv_cs i1 m0)) *
      struct_data_at'_aux ((i0, t0) :: m) m0 sz
     (ListTypeGen (fun it : ident * type => reptype (snd it) -> val -> mpred)
        P ((i0, t0) :: m)) (snd v)).
    rewrite IHm.
    reflexivity.
Qed.

Lemma union_data_at'_aux_spec: forall m sz v P,
  union_data_at'_aux m sz
   (ListTypeGen
     (fun it => reptype (snd it) -> val -> mpred)
     P m) v =
  union_pred m
   (fun it v =>
      withspacer sh
       (sizeof cenv_cs (snd it))
       sz
       (P it v)) v.
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [reflexivity |].
  revert i0 t0 v; induction m as [| (i0, t0) m]; intros.
  + simpl; reflexivity.
  + destruct v as [v | v].
    - reflexivity.
    - apply IHm.
Qed.

End AUXILIARY_PRED.

Module auxiliary_pred.

Import aggregate_pred.

Definition struct_data_at'_aux:
   forall {cs: compspecs} (sh: share) (m m0: members) (sz: Z) (P: ListType (map (fun it => reptype (snd it) -> (val -> mpred)) m)) (v: compact_prod (map (fun it => reptype (snd it)) m)), (val -> mpred)
:= @struct_data_at'_aux.

Definition union_data_at'_aux:
  forall {cs: compspecs} (sh: share) (m: members) (sz: Z) (P: ListType (map (fun it => reptype (snd it) -> (val -> mpred)) m)) (v: compact_sum (map (fun it => reptype (snd it)) m)), (val -> mpred)
:= @union_data_at'_aux.

Definition struct_data_at'_aux_spec: forall {cs: compspecs} (sh: share) m m0 sz v P,
  struct_data_at'_aux sh m m0 sz
   (ListTypeGen
     (fun it => reptype (snd it) -> val -> mpred)
     P m) v =
  struct_pred m 
   (fun it v =>
      withspacer sh
       (field_offset cenv_cs (fst it) m0 + sizeof cenv_cs (snd it))
       (field_offset_next cenv_cs (fst it) m0 sz)
       (at_offset (P it v) (field_offset cenv_cs (fst it) m0))) v
:= @struct_data_at'_aux_spec.

Definition union_data_at'_aux_spec: forall {cs: compspecs} sh m sz v P,
  union_data_at'_aux sh m sz
   (ListTypeGen
     (fun it => reptype (snd it) -> val -> mpred)
     P m) v =
  union_pred m
   (fun it v =>
      withspacer sh
       (sizeof cenv_cs (snd it))
       sz
       (P it v)) v
:= @union_data_at'_aux_spec.

Definition memory_block_array_pred:
  forall {cs: compspecs} {A} sh t z (d: A) b ofs,
  0 <= ofs /\ ofs + sizeof cenv_cs t * Z.max 0 z <= Int.modulus ->
  sizeof cenv_cs t * Z.max 0 z < Int.modulus ->
  array_pred 0 z d
     (fun i _ p =>
      memory_block sh (Int.repr (sizeof cenv_cs t))
        (offset_val (Int.repr (sizeof cenv_cs t * i)) p)) nil
     (Vptr b (Int.repr ofs))  =
  memory_block sh (Int.repr (sizeof cenv_cs t * Z.max 0 z)) (Vptr b (Int.repr ofs))
:= @memory_block_array_pred'.

Definition memory_block_struct_pred:
  forall {cs: compspecs} sh m sz {A} (v: compact_prod (map A m)) b ofs,
  (m = nil -> sz = 0) ->
  members_no_replicate m = true ->
  sizeof_struct cenv_cs 0 m <= sz < Int.modulus ->
  0 <= ofs /\ ofs + sz <= Int.modulus ->
  struct_pred m
   (fun it _ p =>
     (memory_block sh (Int.repr (field_offset_next cenv_cs (fst it) m sz - field_offset cenv_cs (fst it) m)))
     (offset_val (Int.repr (field_offset cenv_cs (fst it) m)) p)) v (Vptr b (Int.repr ofs)) =
  memory_block sh (Int.repr sz) (Vptr b (Int.repr ofs))
:= @memory_block_struct_pred.

Definition memory_block_union_pred:
  forall sh m sz {A} (v: compact_sum (map A m)) b ofs,
  (m = nil -> sz = 0) ->
  union_pred m (fun it _ => memory_block sh (Int.repr sz)) v (Vptr b (Int.repr ofs)) =
  memory_block sh (Int.repr sz) (Vptr b (Int.repr ofs))
:= @memory_block_union_pred.

End auxiliary_pred.
