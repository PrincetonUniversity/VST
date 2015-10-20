Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.type_induction.
Require Import floyd.fieldlist.
Require Import floyd.compact_prod_sum.
Require Import floyd.aggregate_type.
Require Import floyd.mapsto_memory_block.
Require Import floyd.nested_pred_lemmas.
Require Import floyd.jmeq_lemmas.
Require Import floyd.sublist.

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
  fold_range' f zero lo (Z.to_nat (hi-lo)).

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

Inductive Forallz {A} (P: Z -> A->Prop) : Z -> list A -> Prop :=
 | Forallz_nil : forall i, Forallz P i nil
 | Forallz_cons : forall i x l, P i x -> Forallz P (Z.succ i) l -> Forallz P i (x::l).

(******************************************

Definition of aggregate predicates.

******************************************)

Definition array_pred {A: Type} (default: A) (lo hi: Z) (P: Z -> A -> val -> mpred) (v: list A) (p: val) : mpred :=
  rangespec lo (Z.to_nat (hi-lo)) (fun i => P i (Znth (i-lo) v default)) p.

Definition struct_pred (m: members) {A: ident * type -> Type} (P: forall it, A it -> val -> mpred) (v: compact_prod (map A m)) (p: val): mpred.
Proof.
  destruct m as [| (i0, t0) m]; [exact emp |].
  revert i0 t0 v; induction m as [| (i0, t0) m]; intros ? ? v.
  + simpl in v.
    exact (P _ v p).
  + simpl in v.
    exact ((P _ (fst v) p) * IHm i0 t0 (snd v)).
Defined.

(* when unfold, do cbv [struct_pred list_rect]. *)

Definition union_pred (m: members) {A: ident * type -> Type} (P: forall it, A it -> val -> mpred) (v: compact_sum (map A m)) (p: val): mpred.
Proof.
  destruct m as [| (i0, t0) m]; [exact emp |].
  revert i0 t0 v; induction m as [| (i0, t0) m]; intros ? ? v.
  + simpl in v.
    exact (P _ v p).
  + simpl in v.
    destruct v as [v | v].
    - exact (P _ v p).
    - exact (IHm i0 t0 v).
Defined.

Definition array_Prop {A: Type} (d:A) (lo hi: Z) (P: Z -> A -> Prop) (v: list A) : Prop :=
   Zlength v = hi-lo /\ Forallz P 0 v.

Definition struct_Prop (m: members) {A: ident * type -> Type} 
                             (P: forall it, A it -> Prop) (v: compact_prod (map A m)) : Prop.
Proof.
  destruct m as [| (i0, t0) m]; [exact True |].
  revert i0 t0 v; induction m as [| (i0, t0) m]; intros ? ? v.
  + simpl in v.
    exact (P _ v).
  + simpl in v.
    exact ((P _ (fst v)) /\ IHm i0 t0 (snd v)).
Defined.

Definition union_Prop (m: members) {A: ident * type -> Type} 
               (P: forall it, A it -> Prop) (v: compact_sum (map A m)): Prop.
Proof.
  destruct m as [| (i0, t0) m]; [exact True |].
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

Lemma array_pred_len_0: forall {A} (d: A) lo hi P v p,
  hi <= lo ->
  array_pred d lo hi P v p = emp.
Proof.
  intros.
  unfold array_pred.
  replace (Z.to_nat (hi - lo)) with 0%nat by (symmetry; apply nat_of_Z_neg; omega).
  reflexivity.
Qed.

Lemma array_pred_len_1: forall {A} (d:A) i P v p,
  array_pred d i (i + 1) P v p = P i (nth 0 v d) p.
Proof.
  intros.
  unfold array_pred.
  replace (i + 1 - i) with 1 by omega.
  simpl. rewrite sepcon_emp.
  unfold Znth. rewrite Z.sub_diag. rewrite if_false by omega. change (Z.to_nat 0) with 0%nat. auto.
Qed. 

Lemma split_array_pred: forall {A}  (d: A) lo mid hi P v p,
  lo <= mid <= hi ->
  Zlength v = (hi-lo) ->
  array_pred d lo hi P v p =
  array_pred d lo mid P (sublist 0 (mid-lo) v) p *
  array_pred d mid hi P (sublist (mid-lo) (hi-lo) v) p. 
Proof.
intros.
unfold sublist.
simpl skipn. rewrite Z.sub_0_r.
replace (hi-lo-(mid-lo)) with (hi-mid) by omega.
rewrite (Zfirstn_exact_length (hi-mid))
 by (rewrite Zlength_skipn, (Z.max_r 0 (mid-lo)), Z.max_r  by omega; omega).
clear H0.
unfold array_pred.
remember (Z.to_nat (mid-lo)) as n.
replace (Z.to_nat (hi-lo)) with (n + Z.to_nat (hi-mid))%nat in *
  by (subst n; rewrite <- Z2Nat.inj_add by omega; f_equal; omega).
assert (lo = mid - Z.of_nat n).
  rewrite Heqn. rewrite Z2Nat.id by omega. omega.
subst lo.
clear Heqn.
revert v  H; induction n; intros.
change (Z.of_nat 0) with 0 in *. 
simpl rangespec at 2. rewrite emp_sepcon.
rewrite Z.sub_0_r; reflexivity.
simpl plus.
unfold rangespec; fold rangespec.
repeat match goal with |- context [(?A * ?B) p] => change ((A*B)p) with (A p * B p) end.
rewrite !sepcon_assoc.
f_equal.
f_equal.
unfold Znth; rewrite !if_false by omega.
rewrite nth_firstn; auto.
clear - H.
apply Nat2Z.inj_lt.
rewrite Z2Nat.id by omega.
rewrite inj_S at 1. omega.
specialize (IHn (skipn 1 v)).
etransitivity; [ | etransitivity; [apply IHn | ]].
rewrite inj_S.
replace (Z.succ (mid - Z.succ (Z.of_nat n))) with (mid - Z.of_nat n) by omega.
apply rangespec_ext; intros.
f_equal.
rewrite Znth_succ; try omega.
f_equal.  omega.
omega. 
f_equal.
rewrite inj_S.
replace (Z.succ (mid - Z.succ (Z.of_nat n))) with (mid - Z.of_nat n)  by omega.
apply rangespec_ext; intros.
f_equal.
symmetry.
rewrite Znth_succ; try omega.
f_equal.
omega.
clear.
destruct n,v; simpl; reflexivity.
rewrite skipn_skipn.
reflexivity.
Qed.

Lemma array_pred_shift: forall {A} (d: A) (lo hi lo' hi' mv : Z) P' P v p,
  lo - lo' = mv ->
  hi - hi' = mv ->
 (forall i i', lo <= i < hi -> i - i' = mv -> P' i' (Znth (i-lo) v d) p = P i (Znth (i-lo) v d) p) -> 
  array_pred d lo' hi' P' v p = array_pred d lo hi P v p.
Proof.
  intros.
  unfold array_pred.
  replace (hi' - lo') with (hi - lo) by omega.
  destruct (zlt hi lo). rewrite Z2Nat_neg by omega. reflexivity. 
  apply pred_ext; apply rangespec_shift_derives; intros.
  rewrite H3; rewrite Z2Nat.id in H2 by omega.
  rewrite H1; auto; omega.
  rewrite <- H3; rewrite Z2Nat.id in H2 by omega.
  rewrite H1; auto; omega.
Qed.

Lemma array_pred_ext_derives: forall {A} (d: A) lo hi P0 P1 v0 v1 p,
  (forall i, lo <= i < hi -> 
    P0 i (Znth (i-lo) v0 d) p |-- P1 i (Znth (i-lo) v1 d) p) -> 
  array_pred d lo hi P0 v0 p |-- array_pred d lo hi P1 v1 p.
Proof.
  intros.
  unfold array_pred.
  normalize.
  apply rangespec_ext_derives.
  intros.
  destruct (zlt hi lo). rewrite Z2Nat_neg  in H0 by omega.
  change (Z.of_nat 0) with 0 in H0. omega.
  rewrite Z2Nat.id in H0 by omega.
  apply H. omega.
Qed.

Lemma array_pred_ext: forall {A} (d:A) lo hi P0 P1 v0 v1 p,
  (forall i, lo <= i < hi -> 
    P0 i (Znth (i-lo) v0 d) p = P1 i (Znth (i-lo) v1 d) p) -> 
  array_pred d lo hi P0 v0 p = array_pred d lo hi P1 v1 p.
Proof.
  intros; apply pred_ext; apply array_pred_ext_derives; intros; auto;
  rewrite H; auto.
Qed.

Lemma at_offset_array_pred: forall  {A} (d:A) lo hi P v ofs p,
  at_offset (array_pred d lo hi P v) ofs p = array_pred d lo hi (fun i v => at_offset (P i v) ofs) v p.
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

Opaque member_dec.

Lemma struct_pred_ext_derives: forall m {A0 A1} (P0: forall it, A0 it -> val -> mpred) (P1: forall it, A1 it -> val -> mpred) v0 v1 p,
  members_no_replicate m = true ->
  (forall i d0 d1, in_members i m ->
     P0 _ (proj_struct i m v0 d0) p |-- P1 _ (proj_struct i m v1 d1) p) ->
  struct_pred m P0 v0 p |-- struct_pred m P1 v1 p.
Proof.
  unfold proj_struct, field_type2.
  intros.
  destruct m as [| (i0, t0) m]; [simpl; auto |].
  revert i0 t0 v0 v1 H H0; induction m as [| (i1, t1) m]; intros.
  + specialize (H0 i0).
    simpl in H0.
    if_tac in H0; [| congruence].
    specialize (H0 v0 v1).
    spec H0; [left; reflexivity |].
    destruct (member_dec (i0, t0) (i0, t0)); [| congruence].
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
      destruct (member_dec (i0, t0) (i0, t0)); [| congruence].
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
        change (if ident_eq i i1
                then Errors.OK t1
                else field_type i m) with (field_type i ((i1, t1) :: m)) in H0.
        destruct (member_dec
             (i,
             match field_type i ((i1, t1) :: m) with
             | Errors.OK t => t
             | Errors.Error _ => Tvoid
             end) (i0, t0)); [congruence |].
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
  destruct m as [| (i0, t0) m]; [auto |].
  revert i0 t0 v; induction m as [| (i1, t1) m]; intros.
  + simpl.
    rewrite at_offset_eq.
    auto.
  + simpl.
    rewrite at_offset_eq.
    f_equal.
Qed.

Lemma andp_struct_pred: forall m {A} (P: forall it, A it -> val -> mpred) v p Q R,
  !! (Q /\ struct_Prop m R v) && struct_pred m P v p =
  match m with
  | nil => !! Q && emp
  | _ => struct_pred m (fun it v p => !! (Q /\ R it v) && P it v p) v p
  end.
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [simpl; f_equal; apply ND_prop_ext; tauto |].
  revert i0 t0 v; induction m as [| (i1, t1) m]; intros.
  + simpl.
    auto.
  + change (struct_pred ((i0, t0) :: (i1, t1) :: m) P v p)
      with (P (i0, t0) (fst v) p * struct_pred ((i1, t1) :: m) P (snd v) p).
    change (struct_Prop ((i0, t0) :: (i1, t1) :: m) R v)
      with (R (i0, t0) (fst v) /\ struct_Prop ((i1, t1) :: m) R (snd v)).
    rewrite !prop_and.
    pattern (!! Q) at 1; rewrite <- (andp_dup (!! Q)).
    rewrite !andp_assoc.
    rewrite <- corable_sepcon_andp1 by auto.
    rewrite <- corable_andp_sepcon1 by auto.
    rewrite <- corable_sepcon_andp1 by auto.
    rewrite <- corable_andp_sepcon1 by auto.
    rewrite <- !andp_assoc.
    rewrite <- !prop_and.
    rewrite IHm.
    reflexivity.
Qed.

Lemma compact_sum_inj_eq_spec: forall {A} a0 a1 (l: list A) F0 F1 (v0: compact_sum (map F0 (a0 :: a1 :: l))) (v1: compact_sum (map F1 (a0 :: a1 :: l))) H,
  ~ In a0 (a1 :: l) ->
 ((forall a, compact_sum_inj v0 a H <-> compact_sum_inj v1 a H) <->
  match v0, v1 with
  | inl _, inl _ => True
  | inr v0, inr v1 => forall a, compact_sum_inj (v0: compact_sum (map F0 (a1 :: l))) a H <-> compact_sum_inj (v1: compact_sum (map F1 (a1 :: l))) a H
  | _, _ => False
  end).
Proof.
  intros.
  rename H0 into H_not_in.
  destruct v0, v1.
  + simpl.
    firstorder.
  + assert (~ (forall a : A,
      iff
        (@compact_sum_inj A F0 (@cons A a0 (@cons A a1 l))
           (@inl (F0 a0) (compact_sum (@map A Type F0 (@cons A a1 l))) f) a H)
        (@compact_sum_inj A F1 (@cons A a0 (@cons A a1 l))
           (@inr (F1 a0) (compact_sum (@map A Type F1 (@cons A a1 l))) c) a H))); [| tauto].
    intro.
    specialize (H0 a0).
    simpl in H0.
    destruct (H a0 a0); [| congruence].
    tauto.
  + assert (~ (forall a : A,
      iff
        (@compact_sum_inj A F0 (@cons A a0 (@cons A a1 l))
           (@inr (F0 a0) (compact_sum (@map A Type F0 (@cons A a1 l))) c) a H)
        (@compact_sum_inj A F1 (@cons A a0 (@cons A a1 l))
           (@inl (F1 a0) (compact_sum (@map A Type F1 (@cons A a1 l))) f) a H))); [| tauto].
    intro.
    specialize (H0 a0).
    simpl in H0.
    destruct (H a0 a0); [| congruence].
    tauto.
  + split; intros HH a; specialize (HH a).
    - pose proof compact_sum_inj_in c a H.
      pose proof compact_sum_inj_in c0 a H.
Opaque In.
      simpl in HH, H0, H1 |- *.
Transparent In.
      destruct (H a a0).
      * subst.
        tauto.
      * tauto.
    - simpl in HH |- *.
      destruct (H a a0).
      * tauto.
      * tauto.
Qed.

Lemma union_pred_ext_derives: forall m {A0 A1} (P0: forall it, A0 it -> val -> mpred) (P1: forall it, A1 it -> val -> mpred) v0 v1 p,
  members_no_replicate m = true ->
  (forall it, members_union_inj v0 it <-> members_union_inj v1 it) ->
  (forall i d0 d1, members_union_inj v0 (i, field_type2 i m) -> members_union_inj v1 (i, field_type2 i m) ->
     P0 _ (proj_union i m v0 d0) p |-- P1 _ (proj_union i m v1 d1) p) ->
  union_pred m P0 v0 p |-- union_pred m P1 v1 p.
Proof.
  unfold members_union_inj, proj_union, field_type2.
  intros.
  destruct m as [| (i0, t0) m]; [simpl; auto |].
  revert i0 t0 v0 v1 H H0 H1; induction m as [| (i1, t1) m]; intros.
  + specialize (H1 i0).
    simpl in H1.
    if_tac in H1; [| congruence].
    specialize (H1 v0 v1).
    spec H1; [if_tac; [auto | congruence] |].
    spec H1; [if_tac; [auto | congruence] |].
    destruct (member_dec (i0, t0) (i0, t0)); [| congruence].
    unfold eq_rect_r in H1; rewrite <- !eq_rect_eq in H1.
    simpl.
    exact H1.
  + rewrite compact_sum_inj_eq_spec in H0.
    Focus 2. {
      clear - H.
      pose proof in_members_tail_no_replicate i0 _ _ _ H.
      intro HH; apply in_map with (f := fst) in HH.
      apply H0 in HH.
      tauto.
    } Unfocus.
    destruct v0 as [v0 | v0], v1 as [v1 | v1]; try solve [inversion H0].
    - specialize (H1 i0).
      simpl in H1.
      if_tac in H1; [| congruence].
      specialize (H1 v0 v1).
      spec H1; [if_tac; [auto | congruence] |].
      spec H1; [if_tac; [auto | congruence] |].
      destruct (member_dec (i0, t0) (i0, t0)); [| congruence].
      unfold eq_rect_r in H1; rewrite <- !eq_rect_eq in H1.
      simpl.
      exact H1.
    - rewrite members_no_replicate_ind in H.
      apply IHm; [tauto | tauto |].
      intros.
      specialize (H1 i).
      simpl in H1.
      if_tac in H1. (* i = i0 vs i <> i0 *)
      * clear - H H2 H4 t0.
        pose proof compact_sum_inj_in v0 (i, field_type2 i ((i1, t1) :: m)) member_dec.
        spec H0; [exact H2 |].
        subst.
        apply in_map with (f := fst) in H0.
        unfold fst at 1 in H0.
        tauto.
      * specialize (H1 d0 d1).
        change (if ident_eq i i1
                then Errors.OK t1
                else field_type i m) with (field_type i ((i1, t1) :: m)) in H1.
        destruct (member_dec
             (i,
             match field_type i ((i1, t1) :: m) with
             | Errors.OK t => t
             | Errors.Error _ => Tvoid
             end) (i0, t0)); [congruence |].
        spec H1; [auto |].
        spec H1; [auto |].
        exact H1.
Qed.

Lemma union_pred_ext: forall m {A0 A1} (P0: forall it, A0 it -> val -> mpred) (P1: forall it, A1 it -> val -> mpred) v0 v1 p,
  members_no_replicate m = true ->
  (forall it, members_union_inj v0 it <-> members_union_inj v1 it) ->
  (forall i d0 d1, members_union_inj v0 (i, field_type2 i m) -> members_union_inj v1 (i, field_type2 i m) ->
     P0 _ (proj_union i m v0 d0) p = P1 _ (proj_union i m v1 d1) p) ->
  union_pred m P0 v0 p = union_pred m P1 v1 p.
Proof.
  intros.
  assert (forall it, members_union_inj v1 it <-> members_union_inj v0 it)
    by (intro it; specialize (H0 it); tauto).
  apply pred_ext; eapply union_pred_ext_derives; auto;
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

Lemma andp_union_pred: forall m {A} (P: forall it, A it -> val -> mpred) v p Q R,
  !! (Q /\ union_Prop m R v) && union_pred m P v p =
  match m with
  | nil => !! Q && emp
  | _ => union_pred m (fun it v p => !! (Q /\ R it v) && P it v p) v p
  end.
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [simpl; f_equal; apply ND_prop_ext; tauto |].
  revert i0 t0 v; induction m as [| (i1, t1) m]; intros.
  + simpl.
    auto.
  + destruct v.
    - simpl.
      auto.
    - simpl.
      apply IHm.
Qed.

Section MEMORY_BLOCK_AGGREGATE.

Context {cs: compspecs}.

Lemma memory_block_array_pred: forall  {A} (d:A) sh t lo hi v b ofs,
  0 <= ofs + sizeof cenv_cs t * lo /\ ofs + sizeof cenv_cs t * hi <= Int.modulus ->
  0 <= lo <= hi ->
  sizeof cenv_cs t * (hi - lo) < Int.modulus ->
  array_pred d lo hi
    (fun i _ p => memory_block sh (sizeof cenv_cs t) (offset_val (Int.repr (sizeof cenv_cs t * i)) p)) v
    (Vptr b (Int.repr ofs)) =
   memory_block sh (sizeof cenv_cs t * (hi - lo)) (Vptr b (Int.repr (ofs + sizeof cenv_cs t * lo))).
Proof.
  intros.
  unfold array_pred.
  f_equal.
  remember (Z.to_nat (hi - lo)) as n eqn:HH.
  revert lo HH H H0 H1 v; induction n; intros.
  + simpl.
    pose proof arith_aux00 _ _ (proj2 H0) HH.
    rewrite H2, Z.mul_0_r, memory_block_zero_Vptr.
    reflexivity.
  + simpl.
    pose proof arith_aux01 _ _ _ HH.
    solve_mod_modulus.
    pose_size_mult cenv_cs t (0 :: hi - Z.succ lo :: hi - lo :: nil).
    rewrite IHn; [| apply arith_aux02; auto | omega | omega | omega | exact v].
    replace (ofs + sizeof cenv_cs t * Z.succ lo) with (ofs + sizeof cenv_cs t * lo + sizeof cenv_cs t) by omega.
    rewrite <- memory_block_split by (auto; omega).
    f_equal.
    omega.
Qed.

Lemma memory_block_array_pred': forall {A} (d:A)  sh t z b ofs,
  0 <= z ->
  0 <= ofs /\ ofs + sizeof cenv_cs t * z <= Int.modulus ->
  sizeof cenv_cs t * z < Int.modulus ->
  array_pred d 0 z
     (fun i _ p =>
      memory_block sh (sizeof cenv_cs t) (offset_val (Int.repr (sizeof cenv_cs t * i)) p))
             (list_repeat (Z.to_nat z) d)
     (Vptr b (Int.repr ofs))  =
  memory_block sh (sizeof cenv_cs t * z) (Vptr b (Int.repr ofs)).
Proof.
  intros.
  rewrite memory_block_array_pred.
  f_equal. f_equal. omega. f_equal. f_equal. rewrite Z.mul_0_r. omega.
  rewrite Z.mul_0_r. split; omega. omega.
  rewrite Z.sub_0_r. auto.
Qed.

Lemma memory_block_struct_pred: forall sh m sz {A} (v: compact_prod (map A m)) b ofs,
  (m = nil -> sz = 0) ->
  members_no_replicate m = true ->
  sizeof_struct cenv_cs 0 m <= sz < Int.modulus ->
  0 <= ofs /\ ofs + sz <= Int.modulus ->
  struct_pred m
   (fun it _ p =>
     (memory_block sh (field_offset_next cenv_cs (fst it) m sz - field_offset2 cenv_cs (fst it) m))
     (offset_val (Int.repr (field_offset2 cenv_cs (fst it) m)) p)) v (Vptr b (Int.repr ofs)) =
  memory_block sh sz (Vptr b (Int.repr ofs)).
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
      f_equal; omega.
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
  union_pred m (fun it _ => memory_block sh sz) v (Vptr b (Int.repr ofs)) =
  memory_block sh sz (Vptr b (Int.repr ofs)).
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

Section EMPTY_AGGREGATE.

Context {cs: compspecs}.

Lemma emp_array_pred: forall {A} (d:A) lo hi v p,
  array_pred d lo hi (fun _ _ _ => emp) v p =  emp.
Proof.
  intros.
  unfold array_pred.
  forget (Z.to_nat (hi-lo)) as n.
  revert lo; induction n; simpl; intros. auto.
  rewrite emp_sepcon; auto.
Qed.

Lemma emp_struct_pred: forall m {A} (v: compact_prod (map A m)) p,
  struct_pred m (fun _ _ _ => emp) v p = emp.
Proof.
  intros.
  destruct m as [| (i0, t0) m].
  + simpl. auto.
  + revert i0 t0 v; induction m as [| (i1, t1) m]; intros.
    - simpl. auto.
    - change (struct_pred ((i0, t0) :: (i1, t1) :: m) (fun _ _ _ => emp) v p) with
        (emp * struct_pred ((i1, t1) :: m) (fun _ _ _ => emp) (snd v) p).
      rewrite IHm.
      apply sepcon_emp.
Qed.

Lemma emp_union_pred: forall m {A} (v: compact_sum (map A m)) p,
  union_pred m (fun _ _ _ => emp) v p = emp.
Proof.
  intros.
  destruct m as [| (i0, t0) m].
  + simpl. auto.
  + revert i0 t0 v; induction m as [| (i1, t1) m]; intros.
    - simpl. auto.
    - destruct v as [v | v].
      * simpl. auto.
      * change (union_pred ((i0, t0) :: (i1, t1) :: m) (fun _ _ _ => emp) (inr v) p) with
          (union_pred ((i1, t1) :: m) (fun _ _ _ => emp) v p).
        apply IHm.
Qed.

End EMPTY_AGGREGATE.

Module aggregate_pred.

Open Scope Z.
Open Scope logic.
Export floyd.aggregate_type.aggregate_type.

Definition array_pred: forall {A: Type} (d:A) (lo hi: Z) (P: Z -> A -> val -> mpred) (v: list A),
    val -> mpred := @array_pred.

Definition struct_pred: forall (m: members) {A: ident * type -> Type} (P: forall it, A it -> val -> mpred) (v: compact_prod (map A m)) (p: val), mpred := @struct_pred.

Definition union_pred: forall (m: members) {A: ident * type -> Type} (P: forall it, A it -> val -> mpred) (v: compact_sum (map A m)) (p: val), mpred := @union_pred.

Definition array_Prop: forall {A: Type} (d:A) (lo hi: Z) (P: Z -> A -> Prop) (v: list A), Prop := @array_Prop.

Definition struct_Prop: forall (m: members) {A: ident * type -> Type} (P: forall it, A it -> Prop) (v: compact_prod (map A m)), Prop := @struct_Prop.

Definition union_Prop: forall (m: members) {A: ident * type -> Type} (P: forall it, A it -> Prop) (v: compact_sum (map A m)), Prop := union_Prop.

Definition array_pred_len_0: forall {A} (d:A) lo hi P v p,
  hi <= lo ->
  array_pred d lo hi P v p = emp
:= @array_pred_len_0.

Definition array_pred_len_1: forall {A} (d:A) i P v p,
  array_pred d i (i + 1) P v p =  P i (nth 0 v d) p
:= @array_pred_len_1.

Definition split_array_pred: forall  {A} (d:A) lo mid hi P v p,
  lo <= mid <= hi ->
  Zlength v = (hi-lo) ->
  array_pred d lo hi P v p =
  array_pred d lo mid P (sublist 0 (mid-lo) v) p *
  array_pred d mid hi P (sublist (mid-lo) (hi-lo) v) p
:= @split_array_pred.

Definition array_pred_shift: forall {A} (d:A) lo hi lo' hi' mv P' P v p,
  lo - lo' = mv ->
  hi - hi' = mv ->
  (forall i i', lo <= i < hi -> i - i' = mv -> P' i' (Znth (i - lo) v d) p = P i (Znth (i - lo) v d) p) -> 
  array_pred d lo' hi' P' v p = array_pred d lo hi P v p
:= @array_pred_shift.

Definition array_pred_ext_derives:
  forall {A} (d:A) lo hi P0 P1 v0 v1 p,
  (forall i, lo <= i < hi -> 
      P0 i (Znth (i-lo) v0 d) p |-- P1 i (Znth (i-lo) v1 d) p) -> 
  array_pred d lo hi P0 v0 p |-- array_pred d lo hi P1 v1 p
:= @array_pred_ext_derives.

Definition array_pred_ext:
  forall {A} (d:A) lo hi P0 P1 v0 v1 p,
  (forall i, lo <= i < hi -> 
     P0 i (Znth (i - lo) v0 d) p = P1 i (Znth (i - lo) v1 d) p) -> 
  array_pred d lo hi P0 v0 p = array_pred d lo hi P1 v1 p
:= @array_pred_ext.

Definition at_offset_array_pred: forall {A} (d:A) lo hi P v ofs p,
  at_offset (array_pred d lo hi P v) ofs p = array_pred d lo hi (fun i v => at_offset (P i v) ofs) v p
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

Definition andp_struct_pred: forall m {A} (P: forall it, A it -> val -> mpred) v p Q R,
  !! (Q /\ struct_Prop m R v) && struct_pred m P v p =
  match m with
  | nil => !! Q && emp
  | _ => struct_pred m (fun it v p => !! (Q /\ R it v) && P it v p) v p
  end
:= @andp_struct_pred.

Definition union_pred_ext_derives:
  forall m {A0 A1} (P0: forall it, A0 it -> val -> mpred) (P1: forall it, A1 it -> val -> mpred) v0 v1 p,
  members_no_replicate m = true ->
  (forall it, members_union_inj v0 it <-> members_union_inj v1 it) ->
  (forall i d0 d1, members_union_inj v0 (i, field_type i m) -> members_union_inj v1 (i, field_type i m) ->
     P0 _ (proj_union i m v0 d0) p |-- P1 _ (proj_union i m v1 d1) p) ->
  union_pred m P0 v0 p |-- union_pred m P1 v1 p
:= @union_pred_ext_derives.

Definition union_pred_ext:
  forall m {A0 A1} (P0: forall it, A0 it -> val -> mpred) (P1: forall it, A1 it -> val -> mpred) v0 v1 p,
  members_no_replicate m = true ->
  (forall it, members_union_inj v0 it <-> members_union_inj v1 it) ->
  (forall i d0 d1, members_union_inj v0 (i, field_type i m) -> members_union_inj v1 (i, field_type i m) ->
     P0 _ (proj_union i m v0 d0) p = P1 _ (proj_union i m v1 d1) p) ->
  union_pred m P0 v0 p = union_pred m P1 v1 p
:= @union_pred_ext.

Definition at_offset_union_pred: forall m {A} (P: forall it, A it -> val -> mpred) v p ofs,
  at_offset (union_pred m P v) ofs p = union_pred m (fun it v => at_offset (P it v) ofs) v p
:= at_offset_union_pred.

Definition andp_union_pred: forall m {A} (P: forall it, A it -> val -> mpred) v p Q R,
  !! (Q /\ union_Prop m R v) && union_pred m P v p =
  match m with
  | nil => !! Q && emp
  | _ => union_pred m (fun it v p => !! (Q /\ R it v) && P it v p) v p
  end
:= @andp_union_pred.

End aggregate_pred.

Require Import floyd.reptype_lemmas.

(******************************************

Auxiliary predicates

******************************************)

Section AUXILIARY_PRED.

Context {cs: compspecs}.

Variable sh: share.

Definition struct_data_at'_aux (m m0: members) (sz: Z) (P: ListType (map (fun it => reptype (field_type2 (fst it) m0) -> (val -> mpred)) m)) (v: compact_prod (map (fun it => reptype (field_type2 (fst it) m0)) m)) : (val -> mpred).
Proof.
  destruct m as [| (i0, t0) m]; [exact (fun _ => emp) |].
  revert i0 t0 v P; induction m as [| (i0, t0) m]; intros ? ? v P.
  + simpl in v, P.
    inversion P; subst.
    exact (withspacer sh
            (field_offset2 cenv_cs i0 m0 + sizeof cenv_cs (field_type2 i0 m0))
            (field_offset_next cenv_cs i0 m0 sz)
            (at_offset (a v) (field_offset2 cenv_cs i0 m0))).
  + simpl in v, P.
    destruct (ident_eq i1 i1); [| congruence].
    inversion P; subst.
    exact (withspacer sh
            (field_offset2 cenv_cs i1 m0 + sizeof cenv_cs (field_type2 i1 m0))
            (field_offset_next cenv_cs i1 m0 sz)
            (at_offset (a (fst v)) (field_offset2 cenv_cs i1 m0)) * IHm i0 t0 (snd v) b)%logic.
Defined.

Definition union_data_at'_aux (m m0: members) (sz: Z) (P: ListType (map (fun it => reptype (field_type2 (fst it) m0) -> (val -> mpred)) m)) (v: compact_sum (map (fun it => reptype (field_type2 (fst it) m0)) m)) : (val -> mpred).
Proof.
  destruct m as [| (i0, t0) m]; [exact (fun _ => emp) |].
  revert i0 t0 v P; induction m as [| (i0, t0) m]; intros ? ? v P.
  + simpl in v, P.
    inversion P; subst.
    exact (withspacer sh (sizeof cenv_cs (field_type2 i0 m0)) sz (a v)).
  + simpl in v, P.
    inversion P; subst.
    destruct v as [v | v].
    - exact (withspacer sh (sizeof cenv_cs (field_type2 i1 m0)) sz (a v)).
    - exact (IHm i0 t0 v b).
Defined.

Lemma struct_data_at'_aux_spec: forall m m0 sz v P,
  struct_data_at'_aux m m0 sz
   (ListTypeGen
     (fun it => reptype (field_type2 (fst it) m0) -> val -> mpred)
     P m) v =
  struct_pred m 
   (fun it v =>
      withspacer sh
       (field_offset2 cenv_cs (fst it) m0 + sizeof cenv_cs (field_type2 (fst it) m0))
       (field_offset_next cenv_cs (fst it) m0 sz)
       (at_offset (P it v) (field_offset2 cenv_cs (fst it) m0))) v.
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [reflexivity |].
  revert i0 t0 v; induction m as [| (i0, t0) m]; intros.
  + simpl; reflexivity.
  + replace
     (struct_data_at'_aux ((i1, t1) :: (i0, t0) :: m) m0 sz
     (ListTypeGen (fun it : ident * type => reptype (field_type2 (fst it) m0) -> val -> mpred)
        P ((i1, t1) :: (i0, t0) :: m)) v) with
     (withspacer sh
       (field_offset2 cenv_cs i1 m0 + sizeof cenv_cs (field_type2 i1 m0))
         (field_offset_next cenv_cs i1 m0 sz)
           (at_offset (P (i1, t1) (fst v)) (field_offset2 cenv_cs i1 m0)) *
      struct_data_at'_aux ((i0, t0) :: m) m0 sz
     (ListTypeGen (fun it : ident * type => reptype (field_type2 (fst it) m0) -> val -> mpred)
        P ((i0, t0) :: m)) (snd v))%logic.
    - rewrite IHm.
      reflexivity.
    - simpl.
      destruct (ident_eq i1 i1); [| congruence].
      reflexivity.
Qed.

Lemma union_data_at'_aux_spec: forall m m0 sz v P,
  union_data_at'_aux m m0 sz
   (ListTypeGen
     (fun it => reptype (field_type2 (fst it) m0) -> val -> mpred)
     P m) v =
  union_pred m
   (fun it v =>
      withspacer sh
       (sizeof cenv_cs (field_type2 (fst it) m0))
       sz
       (P it v)) v.
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [reflexivity |].
  revert i0 t0 v; induction m as [| (i0, t0) m]; intros.
  + simpl. unfold union_pred. simpl. reflexivity.
  + destruct v as [v | v].
    - reflexivity.
    - apply IHm.
Qed.

Definition struct_value_fits_aux (m m0: members)
      (P: ListType (map (fun it => reptype (field_type2 (fst it) m0) -> Prop) m))
      (v: compact_prod (map (fun it => reptype (field_type2 (fst it) m0)) m)) : Prop.
Proof.
  destruct m as [| (i0, t0) m]; [exact True |].
  revert i0 t0 v P; induction m as [| (i0, t0) m]; intros ? ? v P.
  + simpl in v, P.
    inversion P; subst.
    apply (a v).
  + simpl in v, P.
    destruct (ident_eq i1 i1); [| congruence].
    inversion P; subst.
    apply (a (fst v) /\ IHm i0 t0 (snd v) b).
Defined.

Definition union_value_fits_aux (m m0: members)
      (P: ListType (map (fun it => reptype (field_type2 (fst it) m0) -> Prop) m)) 
      (v: compact_sum (map (fun it => reptype (field_type2 (fst it) m0)) m)) : Prop.
Proof.
  destruct m as [| (i0, t0) m]; [exact True |].
  revert i0 t0 v P; induction m as [| (i0, t0) m]; intros ? ? v P.
  + simpl in v, P.
    inversion P; subst.
    exact (a v).
  + simpl in v, P.
    inversion P; subst.
    destruct v as [v | v].
    - exact (a v).
    - exact (IHm i0 t0 v b).
Defined.

Lemma struct_value_fits_aux_spec: forall m m0 v P,
  struct_value_fits_aux m m0
   (ListTypeGen
     (fun it => reptype (field_type2 (fst it) m0) -> Prop)
     P m) v =
  struct_Prop m P v.
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [reflexivity |].
  revert i0 t0 v; induction m as [| (i0, t0) m]; intros.
  + simpl; reflexivity.
  + replace
     (struct_value_fits_aux ((i1, t1) :: (i0, t0) :: m) m0
     (ListTypeGen (fun it : ident * type => reptype (field_type2 (fst it) m0) -> Prop)
        P ((i1, t1) :: (i0, t0) :: m)) v) with
     (P (i1, t1) (fst v) /\  struct_value_fits_aux ((i0, t0) :: m) m0 
     (ListTypeGen (fun it : ident * type => reptype (field_type2 (fst it) m0) -> Prop)
        P ((i0, t0) :: m)) (snd v)).
    - rewrite IHm.
      reflexivity.
    - simpl.
      destruct (ident_eq i1 i1); [| congruence].
      reflexivity.
Qed.

Lemma union_value_fits_aux_spec: forall m m0 v P,
  union_value_fits_aux m m0
   (ListTypeGen
     (fun it => reptype (field_type2 (fst it) m0) -> Prop)
     P m) v =
  union_Prop m P v.
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [reflexivity |].
  revert i0 t0 v; induction m as [| (i0, t0) m]; intros.
  + simpl. unfold union_Prop. simpl. reflexivity.
  + destruct v as [v | v].
    - reflexivity.
    - apply IHm.
Qed.

End AUXILIARY_PRED.

Module auxiliary_pred.

Import aggregate_pred.

Definition struct_data_at'_aux:
   forall {cs: compspecs} (sh: share) (m m0: members) (sz: Z) (P: ListType (map (fun it => reptype (field_type (fst it) m0) -> (val -> mpred)) m)) (v: compact_prod (map (fun it => reptype (field_type (fst it) m0)) m)), (val -> mpred)
:= @struct_data_at'_aux.

Definition union_data_at'_aux:
  forall {cs: compspecs} (sh: share) (m m0: members) (sz: Z) (P: ListType (map (fun it => reptype (field_type (fst it) m0) -> (val -> mpred)) m)) (v: compact_sum (map (fun it => reptype (field_type (fst it) m0)) m)), (val -> mpred)
:= @union_data_at'_aux.

Definition struct_data_at'_aux_spec: forall {cs: compspecs} (sh: share) m m0 sz v P,
  struct_data_at'_aux sh m m0 sz
   (ListTypeGen
     (fun it => reptype (field_type (fst it) m0) -> val -> mpred)
     P m) v =
  struct_pred m 
   (fun it v =>
      withspacer sh
       (field_offset2 cenv_cs (fst it) m0 + sizeof cenv_cs (field_type (fst it) m0))
       (field_offset_next cenv_cs (fst it) m0 sz)
       (at_offset (P it v) (field_offset2 cenv_cs (fst it) m0))) v
:= @struct_data_at'_aux_spec.

Definition union_data_at'_aux_spec: forall {cs: compspecs} sh m m0 sz v P,
  union_data_at'_aux sh m m0 sz
   (ListTypeGen
     (fun it => reptype (field_type (fst it) m0) -> val -> mpred)
     P m) v =
  union_pred m
   (fun it v =>
      withspacer sh
       (sizeof cenv_cs (field_type (fst it) m0))
       sz
       (P it v)) v
:= @union_data_at'_aux_spec.

Definition struct_value_fits_aux:
  forall {cs: compspecs} (m m0: members)
      (P: ListType (map (fun it => reptype (field_type2 (fst it) m0) -> Prop) m))
      (v: compact_prod (map (fun it => reptype (field_type2 (fst it) m0)) m)), Prop
:= @struct_value_fits_aux.

Definition union_value_fits_aux:
  forall {cs: compspecs} (m m0: members)
      (P: ListType (map (fun it => reptype (field_type2 (fst it) m0) -> Prop) m)) 
      (v: compact_sum (map (fun it => reptype (field_type2 (fst it) m0)) m)), Prop
:= @union_value_fits_aux.

Definition struct_value_fits_aux_spec: forall {cs: compspecs} m m0 v P,
  struct_value_fits_aux m m0
   (ListTypeGen
     (fun it => reptype (field_type2 (fst it) m0) -> Prop)
     P m) v =
  struct_Prop m P v
:= @struct_value_fits_aux_spec.

Definition union_value_fits_aux_spec: forall {cs: compspecs} m m0 v P,
  union_value_fits_aux m m0
   (ListTypeGen
     (fun it => reptype (field_type2 (fst it) m0) -> Prop)
     P m) v =
  union_Prop m P v
:= @union_value_fits_aux_spec.

Definition memory_block_array_pred:
  forall {cs: compspecs} (A : Type) (d : A) sh t z b ofs,
  0 <= z ->
  0 <= ofs /\ ofs + sizeof cenv_cs t * z <= Int.modulus ->
  sizeof cenv_cs t * z < Int.modulus ->
  array_pred d 0 z
     (fun i _ p =>
      memory_block sh (sizeof cenv_cs t)
        (offset_val (Int.repr (sizeof cenv_cs t * i)) p)) (list_repeat (Z.to_nat z) d)
     (Vptr b (Int.repr ofs))  =
  memory_block sh (sizeof cenv_cs t * z) (Vptr b (Int.repr ofs))
:= @memory_block_array_pred'.

Definition memory_block_struct_pred:
  forall {cs: compspecs} sh m sz {A} (v: compact_prod (map A m)) b ofs,
  (m = nil -> sz = 0) ->
  members_no_replicate m = true ->
  sizeof_struct cenv_cs 0 m <= sz < Int.modulus ->
  0 <= ofs /\ ofs + sz <= Int.modulus ->
  struct_pred m
   (fun it _ p =>
     (memory_block sh (field_offset_next cenv_cs (fst it) m sz - field_offset cenv_cs (fst it) m))
     (offset_val (Int.repr (field_offset cenv_cs (fst it) m)) p)) v (Vptr b (Int.repr ofs)) =
  memory_block sh sz (Vptr b (Int.repr ofs))
:= @memory_block_struct_pred.

Definition memory_block_union_pred:
  forall sh m sz {A} (v: compact_sum (map A m)) b ofs,
  (m = nil -> sz = 0) ->
  union_pred m (fun it _ => memory_block sh sz) v (Vptr b (Int.repr ofs)) =
  memory_block sh sz (Vptr b (Int.repr ofs))
:= @memory_block_union_pred.

Definition emp_array_pred: forall {A} (d:A) lo hi v p,
  array_pred d lo hi (fun _ _ _ => emp) v p = emp
:= @emp_array_pred.

Definition emp_struct_pred: forall m {A} (v: compact_prod (map A m)) p,
  struct_pred m (fun _ _ _ => emp) v p = emp
:= @emp_struct_pred.

Definition emp_union_pred: forall m {A} (v: compact_sum (map A m)) p,
  union_pred m (fun _ _ _ => emp) v p = emp
:= @emp_union_pred.

End auxiliary_pred.
