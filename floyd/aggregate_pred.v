Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.type_induction.
Require Import floyd.fieldlist.
Require Import floyd.mapsto_memory_block.
Require Import floyd.jmeq_lemmas.
Require Import Coq.Logic.JMeq.

Open Scope Z.
Open Scope logic.

(******************************************

Definition and lemmas about list and Z

******************************************)

Definition Znth {X} n (xs: list X) (default: X) :=
  if (zlt n 0) then default else nth (Z.to_nat n) xs default.

Lemma Znth_succ: forall {A} i lo (v: list A), Z.succ lo <= i -> Znth (i - lo) v = Znth (i - (Z.succ lo)) (skipn 1 v).
Proof.
  intros.
  extensionality default.
  unfold Znth.
  if_tac; [omega |].
  if_tac; [omega |].
  rewrite nth_skipn.
  f_equal.
  change 1%nat with (Z.to_nat 1).
  rewrite <- Z2Nat.inj_add by omega.
  f_equal.
  omega.
Qed.

Lemma Znth_skipn: forall {A} n xs (default: A),
  0 <= n ->
  Znth 0 (skipn (nat_of_Z n) xs) default = Znth n xs default.
Proof.
  intros.
  unfold Znth.
  if_tac; [omega |].
  if_tac; [omega |].
  rewrite nth_skipn.
  reflexivity.
Qed.

Lemma split3_full_length_list: forall {A} lo mid hi (ct: list A) d,
  lo <= mid < hi ->
  Zlength ct = hi - lo ->
  ct = firstn (Z.to_nat (mid - lo)) ct ++
       (Znth (mid - lo) ct d :: nil) ++
       skipn (Z.to_nat (mid - lo + 1)) ct.
Proof.
  intros.
  rewrite <- firstn_skipn with (l := ct) (n := Z.to_nat (mid - lo)) at 1.
  f_equal.
  rewrite Z2Nat.inj_add by omega.
  rewrite <- skipn_skipn.
  replace (Znth (mid - lo) ct d :: nil) with (firstn (Z.to_nat 1) (skipn (Z.to_nat (mid - lo)) ct)).
  + rewrite firstn_skipn; reflexivity.
  + unfold Znth.
    if_tac; [omega |].
    rewrite firstn_1_skipn; [reflexivity |].
    rewrite <- (Nat2Z.id (length ct)).
    apply Z2Nat.inj_lt.
    - omega.
    - omega.
    - rewrite Zlength_correct in H0.
      omega.
Qed.

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

Section CENV.

Context {cs: compspecs}.

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

Definition union_val {m: members} {A} i (v: A (i, field_type2 i m)) (d: forall it, A it) : compact_sum (map A m).
Proof.
  unfold field_type2 in v.
  destruct m as [| (i0, t0) m]; [exact tt |].
  revert i0 t0 v; induction m as [| (i1, t1) m]; intros.
  + simpl in v |- *.
    if_tac in v.
    - subst; exact v.
    - exact (d (i0, t0)).
  + simpl in v |- *.
    if_tac in v.
    - subst.
      exact (inl v).
    - exact (inr (IHm i1 t1 v)).
Defined.

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

Lemma proj_union_union_val: forall i m A v d (d0: A (i, field_type2 i m)),
  in_members i m ->
  proj_union i m (union_val i v d) d0 = v.
Proof.
  unfold field_type2.
  intros.
  destruct m as [| (i0, t0) m]; [inversion H |].
  revert i0 t0 v d0 H; induction m as [| (i1, t1) m]; intros.
  + inversion H; [subst | tauto].
    simpl in v, d0 |- *.
    clear H.
    if_tac; [| congruence].
    unfold eq_rect_r.
    rewrite <- !eq_rect_eq.
    auto.
  + simpl in v, d0 |- *; subst.
    if_tac.
    - subst;
      unfold eq_rect_r.
      rewrite <- !eq_rect_eq.
      auto.
    - destruct H; [unfold fst in H; congruence |].
      exact (IHm i1 t1 v d0 H).
Qed.

Lemma members_union_inj_union_val: forall A i m (v0: A (i, field_type2 i m)) (v: compact_sum (map A m)) d,
  members_no_replicate m = true ->
  fst (members_union_inj v) = i ->
  members_union_inj v = members_union_inj (union_val i v0 d).
Proof.
  unfold field_type2.
  intros A i m v0 v d NO_REPLI ?.
  destruct m as [| (i0, t0) m]; [auto |].
  revert i0 t0 v0 v H NO_REPLI; induction m as [| (i1, t1) m]; intros.
  + simpl in H; subst.
    auto.
  + simpl in H, v0, v |- *.
    destruct (ident_eq i i0).
    - subst.
      destruct v as [v | v].
      * unfold fst in H; subst.
        unfold eq_rect_r; rewrite <- !eq_rect_eq.
        auto.
      * pose proof members_union_inj_in_members ((i1, t1) :: m) _ v.
        spec H0; [congruence |].
        replace (fst (@members_union_inj ((i1, t1) :: m) _ v)) with i0 in H0 by exact H.
        rewrite members_no_replicate_ind in NO_REPLI; tauto.
    - destruct v as [v | v].
      * unfold fst in H; congruence.
      * apply IHm; [auto | rewrite members_no_replicate_ind in NO_REPLI; tauto].
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

