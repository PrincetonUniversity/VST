Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.floyd.base2.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.type_induction.
Require Import VST.floyd.compact_prod_sum.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.nested_pred_lemmas.
Require Import VST.floyd.jmeq_lemmas.
Require Import VST.zlist.sublist.

Require Export VST.floyd.fieldlist.
Require Export VST.floyd.aggregate_type.

Open Scope Z.

Section mpred.

Context `{!heapGS Σ}.

(******************************************

Definition and lemmas about rangespec

******************************************)

Fixpoint rangespec (lo: Z) (n: nat) (P: Z -> val -> mpred) (p: val) : mpred :=
  match n with
  | O => emp
  | S n' => P lo p ∗ rangespec (Z.succ lo) n' P p
 end.

Fixpoint fold_range' {A: Type} (f: Z -> A -> A) (zero: A) (lo: Z) (n: nat) : A :=
 match n with
  | O => zero
  | S n' => f lo (fold_range' f zero (Z.succ lo) n')
 end.

Definition fold_range {A: Type} (f: Z -> A -> A) (zero: A) (lo hi: Z) : A :=
  fold_range' f zero lo (Z.to_nat (hi-lo)).

Lemma rangespec_shift_derives: forall lo lo' len P P' p p',
  (forall i i', lo <= i < lo + Z_of_nat len -> i - lo = i' - lo' -> P i p ⊢ P' i' p') ->
  rangespec lo len P p ⊢ rangespec lo' len P' p'.
Proof.
  intros.
  revert lo lo' H;
  induction len; intros.
  + simpl. auto.
  + simpl.
    apply bi.sep_mono.
    - apply H; [| lia].
      rewrite Nat2Z.inj_succ.
      rewrite <- Z.add_1_r.
      lia.
    - apply IHlen. intros.
      apply H; [| lia].
      rewrite Nat2Z.inj_succ.
      rewrite <- Z.add_1_r.
      pose proof Zle_0_nat (S len).
      lia.
Qed.

Lemma rangespec_ext_derives: forall lo len P P' p,
  (forall i, lo <= i < lo + Z_of_nat len -> P i p ⊢ P' i p) ->
  rangespec lo len P p ⊢ rangespec lo len P' p.
Proof.
  intros.
  apply rangespec_shift_derives.
  intros.
  assert (i = i') by lia.
  subst.
  apply H.
  auto.
Qed.

Lemma rangespec_shift: forall lo lo' len P P' p p',
  (forall i i', lo <= i < lo + Z_of_nat len -> i - lo = i' - lo' -> P i p = P' i' p') ->
  rangespec lo len P p = rangespec lo' len P' p'.
Proof.
  intros.
  revert lo lo' H;
  induction len; intros.
  + simpl. auto.
  + simpl.
    f_equal.
    - apply H; [| lia].
      rewrite Nat2Z.inj_succ.
      rewrite <- Z.add_1_r.
      lia.
    - apply IHlen. intros.
      apply H; [| lia].
      rewrite Nat2Z.inj_succ.
      rewrite <- Z.add_1_r.
      pose proof Zle_0_nat (S len).
      lia.
Qed.

Lemma rangespec_ext: forall lo len P P' p,
  (forall i, lo <= i < lo + Z_of_nat len -> P i p = P' i p) ->
  rangespec lo len P p = rangespec lo len P' p.
Proof.
  intros; apply rangespec_shift; intros.
  assert (i = i') as <- by lia; auto.
Qed.

Lemma rangespec_sepcon: forall lo len P Q p,
  (rangespec lo len P p ∗ rangespec lo len Q p) = rangespec lo len (fun z v => P z v ∗ Q z v) p.
Proof.
  intros.
  revert lo; induction len; intros.
  + simpl.
    rewrite sep_emp //.
  + simpl.
    rewrite -!sep_assoc; f_equal.
    rewrite -IHlen !sep_assoc; f_equal.
    apply sep_comm.
Qed.

Lemma rangespec_elim: forall lo len P i p,
  lo <= i < lo + Z_of_nat len -> rangespec lo len P p ⊢ <absorb> P i p.
Proof.
  intros. revert lo i H; induction len; intros.
  + simpl in H. lia.
  + simpl. intros; destruct (Z.eq_dec i lo).
    - subst. rewrite /bi_absorbingly. cancel.
    - iIntros "(_ & ?)"; iApply (IHlen with "[$]").
      lia.
Qed.

Inductive Forallz {A} (P: Z -> A -> Prop) : Z -> list A -> Prop :=
 | Forallz_nil : forall i, Forallz P i nil
 | Forallz_cons : forall i x l, P i x -> Forallz P (Z.succ i) l -> Forallz P i (x::l).

(******************************************

Definition of aggregate predicates.

******************************************)

Definition array_pred {A: Type}{d: Inhabitant A}  (lo hi: Z) (P: Z -> A -> val -> mpred) (v: list A) (p: val) : mpred :=
  ⌜Zlength v = hi - lo⌝ ∧
  rangespec lo (Z.to_nat (hi-lo)) (fun i => P i (Znth (i-lo) v)) p.

Definition struct_pred (m: members) {A: member -> Type} (P: forall it, A it -> val -> mpred) (v: compact_prod (map A m)) (p: val): mpred.
Proof.
  destruct m as [| a m]; [exact emp | ].
  revert a v; induction m as [| b m]; intros ? v.
  + simpl in v.
    exact (P _ v p).
  + simpl in v.
    exact ((P _ (fst v) p) ∗ IHm _ (snd v)).
Defined.

(* when unfold, do cbv [struct_pred list_rect]. *)

Definition union_pred (m: members) {A: member -> Type} (P: forall it, A it -> val -> mpred) (v: compact_sum (map A m)) (p: val): mpred.
Proof.
  destruct m as [| a m]; [exact emp |].
  revert a v; induction m as [| b m]; intros ? v.
  + simpl in v.
    exact (P _ v p).
  + simpl in v.
    destruct v as [v | v].
    - exact (P _ v p).
    - exact (IHm _ v).
Defined.

Definition array_Prop {A: Type} (d:A) (lo hi: Z) (P: Z -> A -> Prop) (v: list A) : Prop :=
   Zlength v = hi-lo /\ Forallz P 0 v.

Definition struct_Prop (m: members) {A: member -> Type}
                             (P: forall it, A it -> Prop) (v: compact_prod (map A m)) : Prop.
Proof.
  destruct m as [| a m]; [exact True%type | ].
  revert a v; induction m as [| b m]; intros ? v.
  + simpl in v.
    exact (P _ v).
  + simpl in v.
    exact ((P _ (fst v)) /\ IHm _ (snd v)).
Defined.

Definition union_Prop (m: members) {A: member -> Type}
               (P: forall it, A it -> Prop) (v: compact_sum (map A m)): Prop.
Proof.
  destruct m as [| a m]; [exact True%type |].
  revert a v; induction m as [| b m]; intros ? v.
  + simpl in v.
    exact (P _ v).
  + simpl in v.
    destruct v as [v | v].
    - exact (P _ v).
    - exact (IHm _ v).
Defined.

(******************************************

Properties

******************************************)

Lemma array_pred_len_0: forall {A}{d: Inhabitant A} lo hi P p,
  hi = lo ->
  array_pred lo hi P (@nil A) p = emp.
Proof.
  intros.
  unfold array_pred.
  replace (Z.to_nat (hi - lo)) with 0%nat by (symmetry; apply Z_to_nat_neg; lia).
  simpl.
  rewrite -> prop_true_andp by (unfold Zlength; simpl; lia).
  reflexivity.
Qed.

Lemma array_pred_len_1: forall {A}{d: Inhabitant A} i P (v: A) p,
  array_pred i (i + 1) P (v :: nil) p = P i v p.
Proof.
  intros.
  unfold array_pred.
  replace (i + 1 - i) with 1 by lia.
  simpl. rewrite sep_emp.
  rewrite -> prop_true_andp by (unfold Zlength; simpl; lia).
  unfold Znth. rewrite Z.sub_diag. rewrite -> if_false by lia. auto.
Qed.

Lemma split_array_pred: forall {A}{d: Inhabitant A} lo mid hi P (v: list A) p,
  lo <= mid <= hi ->
  Zlength v = hi - lo ->
  array_pred lo hi P v p =
  (array_pred lo mid P (sublist 0 (mid-lo) v) p ∗
   array_pred mid hi P (sublist (mid-lo) (hi-lo) v) p).
Proof.
  intros.
  unfold array_pred.
  normalize.
  rewrite -> prop_true_andp by (rewrite -> !Zlength_sublist by lia; lia).
  clear H0.
  remember (Z.to_nat (mid-lo)) as n.
  replace (Z.to_nat (hi-lo)) with (n + Z.to_nat (hi-mid))%nat in *
    by (subst n; rewrite <- Z2Nat.inj_add by lia; f_equal; lia).
  assert (lo = mid - Z.of_nat n)
    by (rewrite Heqn; rewrite -> Z2Nat.id by lia; lia).
  clear Heqn.
  revert lo v H H0; induction n; intros.
  + subst lo.
    change (Z.of_nat 0) with 0 in *.
    simpl rangespec at 2. rewrite emp_sep.
    rewrite Z.sub_0_r Z.sub_diag Nat.add_0_l.
    apply rangespec_ext; intros.
    rewrite -> Z2Nat.id in H0 by lia.
    f_equal.
    rewrite -> Znth_sublist, Z.add_0_r by lia.
    reflexivity.
  + simpl plus at 1.
    unfold rangespec; fold rangespec.
    rewrite -sep_assoc; f_equal.
    - rewrite Z.sub_diag.
      subst lo.
      rewrite -> Znth_sublist by (try rewrite Nat2Z.inj_succ; lia).
      reflexivity.
    - erewrite rangespec_ext.
      setoid_rewrite IHn; [|lia..].
      2:{
        intros; simpl.
        rewrite <- Znth_succ by lia; auto.
      }
      rewrite Nat2Z.inj_succ in H0.
      f_equal.
      * apply rangespec_ext; intros.
        rewrite -> Znth_sublist, Z.add_0_r by lia.
        rewrite <- Znth_succ by lia; auto.
        rewrite -> Znth_sublist, Z.add_0_r by lia.
        reflexivity.
      * apply rangespec_ext; intros.
        rewrite -> Z2Nat.id in H1 by lia.
        rewrite -> Znth_sublist by lia.
        rewrite -> Znth_sublist by lia.
        replace (i - mid + (mid - Z.succ lo)) with (i - Z.succ lo) by lia.
        rewrite <- Znth_succ by lia; auto.
        f_equiv; f_equiv; lia.
Qed.

Lemma array_pred_shift: forall {A}{d: Inhabitant A} (lo hi lo' hi' mv : Z) P' P (v: list A) p,
  lo - lo' = mv ->
  hi - hi' = mv ->
 (forall i i', lo <= i < hi -> i - i' = mv -> P' i' (Znth (i-lo) v) p = P i (Znth (i-lo) v) p) ->
  array_pred lo' hi' P' v p = array_pred lo hi P v p.
Proof.
  intros.
  unfold array_pred.
  f_equal; first by f_equal; apply prop_ext; lia.
  replace (hi' - lo') with (hi - lo) by lia.
  destruct (zlt hi lo). rewrite -> Z2Nat_neg by lia. reflexivity.
  apply rangespec_shift; intros.
  rewrite H3; rewrite -> Z2Nat.id in H2 by lia.
  rewrite H1; auto; lia.
Qed.

Lemma array_pred_ext_derives: forall {A B} (dA: Inhabitant A) (dB: Inhabitant B)
         lo hi P0 P1 (v0: list A) (v1: list B) p,
  (Zlength v0 = hi - lo -> Zlength v1 = hi - lo) ->
  (forall i, lo <= i < hi ->
    P0 i (Znth (i-lo) v0) p ⊢ P1 i (Znth (i-lo) v1) p) ->
  array_pred  lo hi P0 v0 p ⊢ array_pred lo hi P1 v1 p.
Proof.
  intros.
  unfold array_pred.
  normalize.
  rewrite -> prop_true_andp by lia.
  apply rangespec_ext_derives.
  intros.
  destruct (zlt hi lo).
  + rewrite -> Z2Nat_neg  in H2 by lia.
    change (Z.of_nat 0) with 0 in H2. lia.
  + rewrite -> Z2Nat.id in H2 by lia.
    apply H0. lia.
Qed.

Lemma array_pred_ext: forall {A B} (dA: Inhabitant A) (dB: Inhabitant B) lo hi P0 P1 
        (v0: list A) (v1: list B) p,
  Zlength v0 = Zlength v1 ->
  (forall i, lo <= i < hi ->
    P0 i (Znth (i-lo) v0) p ⊣⊢ P1 i (Znth (i-lo) v1) p) ->
  array_pred lo hi P0 v0 p ⊣⊢ array_pred lo hi P1 v1 p.
Proof.
  intros; iSplit; iApply array_pred_ext_derives; try rewrite H //; intros; rewrite H0 //.
Qed.

Lemma array_pred_eq: forall {A B} (dA: Inhabitant A) (dB: Inhabitant B) lo hi P0 P1 
        (v0: list A) (v1: list B) p,
  Zlength v0 = Zlength v1 ->
  (forall i, lo <= i < hi ->
    P0 i (Znth (i-lo) v0) p = P1 i (Znth (i-lo) v1) p) ->
  array_pred lo hi P0 v0 p = array_pred lo hi P1 v1 p.
Proof.
  intros.
  unfold array_pred.
  rewrite H; f_equal.
  apply rangespec_ext.
  intros.
  destruct (zlt hi lo).
  + rewrite -> Z2Nat_neg  in H1 by lia.
    change (Z.of_nat 0) with 0 in H1. lia.
  + rewrite -> Z2Nat.id in H1 by lia.
    apply H0. lia.
Qed.

Lemma at_offset_array_pred: forall  {A} {d: Inhabitant A} lo hi P (v: list A) ofs p,
  at_offset (array_pred lo hi P v) ofs p = array_pred lo hi (fun i v => at_offset (P i v) ofs) v p.
Proof.
  intros.
  rewrite at_offset_eq.
  unfold array_pred.
  f_equal.
  apply rangespec_shift.
  intros.
  assert (i = i') by lia; subst i'; clear H0.
  rewrite at_offset_eq.
  auto.
Qed.

Lemma array_pred_sepcon: forall  {A} {d: Inhabitant A} lo hi P Q (v: list A) p,
  (array_pred lo hi P v p ∗ array_pred lo hi Q v p) = array_pred lo hi (fun i a v => P i a v ∗ Q i a v) v p.
Proof.
  intros.
  unfold array_pred.
  normalize.
  f_equal; first by f_equal; apply prop_ext; lia.
  rewrite rangespec_sepcon.
  auto.
Qed.

Opaque member_dec.

Lemma name_member_get:
  forall i m, name_member (get_member i m) = i.
Proof.
induction m; simpl; intros.
auto.
if_tac.
auto.
auto.
Qed.

Lemma struct_pred_ext_derives: forall m {A0 A1} (P0: forall it, A0 it -> val -> mpred) (P1: forall it, A1 it -> val -> mpred) v0 v1 p,
  members_no_replicate m = true ->
  (forall i d0 d1, in_members i m ->
     P0 _ (proj_struct i m v0 d0) p ⊢ P1 _ (proj_struct i m v1 d1) p) ->
  struct_pred m P0 v0 p ⊢ struct_pred m P1 v1 p.
Proof.
  unfold proj_struct, field_type.
  intros.
  destruct m as [| a0 m]; [simpl; auto |].
  revert a0 v0 v1 H H0; induction m as [| a1 m]; intros.
  + specialize (H0 (name_member a0)).
    simpl in H0.
    if_tac in H0; [| congruence].
    specialize (H0 v0 v1).
    spec H0; [left; reflexivity |].
    destruct (member_dec a0 a0); [| congruence].
    unfold eq_rect_r in H0; rewrite <- !eq_rect_eq in H0.
    simpl.
    exact H0.
  + change (struct_pred (a0:: a1 :: m) P0 v0 p) with
      (P0 a0 (fst v0) p ∗ struct_pred (a1 :: m) P0 (snd v0) p).
    change (struct_pred (a0 :: a1 :: m) P1 v1 p) with
      (P1 a0 (fst v1) p ∗ struct_pred (a1 :: m) P1 (snd v1) p).
    apply bi.sep_mono.
    - specialize (H0 (name_member a0)).
      simpl in H0.
      if_tac in H0; [| congruence].
      specialize (H0 (fst v0) (fst v1)).
      spec H0; [left; reflexivity |].
      destruct (member_dec a0 a0); [| congruence].
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
        change (if ident_eq i (name_member a1) then a1 else get_member i m)
                    with (get_member i (a1::m)) in H0.
        destruct (member_dec (get_member i (a1::m)) a0); [ | exact H0].
        exfalso; clear - e H2. subst a0.
        rewrite name_member_get in H2. contradiction.
Qed.

Lemma struct_pred_ext: forall m {A0 A1} (P0: forall it, A0 it -> val -> mpred) (P1: forall it, A1 it -> val -> mpred) v0 v1 p,
  members_no_replicate m = true ->
  (forall i d0 d1, in_members i m ->
     P0 _ (proj_struct i m v0 d0) p ⊣⊢ P1 _ (proj_struct i m v1 d1) p) ->
  struct_pred m P0 v0 p ⊣⊢ struct_pred m P1 v1 p.
Proof.
  intros.
  iSplit; iApply struct_pred_ext_derives; eauto;
    intros; erewrite H0 by eauto; auto.
Qed.

Lemma struct_pred_not_member: forall m {A} (P: forall it, A it -> val -> mpred) (i: ident) v p,
  let P' it := if ident_eq i (name_member it) then fun _ _ => emp else P it in
  ~ in_members i m ->
  struct_pred m P v p = struct_pred m P' v p.
Proof.
  intros.
  destruct m as [| a0 m]; [auto |].
  unfold proj_struct, field_type in *.
  revert a0 H v; induction m as [| a1 m]; intros a0 H.
  + intros; subst P'; simpl.
    rewrite if_false; auto.
    intro; apply H; subst; left; auto.
  + set (M := a1 :: m).
    simpl compact_prod; simpl Ctypes.field_type.
    intros v.
    subst M.
    change (struct_pred (a0:: a1 :: m) P v p)
      with (P _ (fst v) p ∗ struct_pred (a1 :: m) P (snd v) p).
    change (struct_pred (a0 :: a1 :: m) P' v p)
      with (P' _ (fst v) p ∗ struct_pred (a1 :: m) P' (snd v) p).
    destruct (ident_eq i (name_member a0)).
    - subst P'; intros; subst.
      exfalso; apply H.
      left; auto.
    - intros.
      f_equal.
      * unfold P'.
        rewrite -> if_false by auto.
        auto.
      * apply IHm.
        intro; apply H; right; auto.
Qed.

Lemma struct_pred_proj: forall m {A} (P: forall it, A it -> val -> mpred) (i: ident) v p d,
  let P' it := if ident_eq i (name_member it) then fun _ _ => emp else P it in
  members_no_replicate m = true ->
  in_members i m ->
  struct_pred m P v p = (P _ (proj_struct i m v d) p ∗ struct_pred m P' v p).
Proof.
  intros.
  destruct m as [| a0 m]; [inv H0 |].
  unfold proj_struct, field_type in *.
  revert a0 H v d H0; induction m as [| a1 m]; intros.
  + subst P'; simpl in *.
    destruct H0; [simpl in H0; subst i | tauto].
    destruct (ident_eq _ _); [| congruence].
    destruct (member_dec a0 a0); [| congruence].
    unfold eq_rect_r; rewrite <- eq_rect_eq.
    rewrite sep_emp; auto.
  + pose proof H.
    apply members_no_replicate_ind in H1; destruct H1.
    set (M := a1 :: m).
    simpl compact_prod in v |- *; simpl Ctypes.field_type in d |- *.
    subst M.
    change (struct_pred (a0 :: a1 :: m) P v p)
      with (P _ (fst v) p ∗ struct_pred (a1 :: m) P (snd v) p).
    change (struct_pred (a0 :: a1 :: m) P' v p)
      with (P' _ (fst v) p ∗ struct_pred (a1 :: m) P' (snd v) p).
    unfold get_member in d|-*; fold (get_member i (a1::m)) in d|-*.
     destruct (ident_eq i (name_member a0)).
    - f_equal.
      * simpl.
        destruct (member_dec _ _) ; [ | congruence].
        unfold eq_rect_r; rewrite <- eq_rect_eq.
        reflexivity.
      * erewrite struct_pred_not_member by eauto.
        unfold P' at 1.
        rewrite -> if_true by auto.
        rewrite emp_sep.
        subst i. auto.
    - intros.
      destruct H0; [simpl in H0; congruence |].
      rewrite sep_assoc (sep_comm _ (P' _ _ _)) -sep_assoc.
      f_equal.
      * unfold P'.
        rewrite -> if_false by (simpl; congruence).
        auto.
      * erewrite IHm by eauto.
        f_equal.
        simpl.
        change (if ident_eq i (name_member a1) then a1 else get_member i m) with (get_member i (a1::m)).
        destruct (member_dec (get_member i (a1::m)) a0).
        exfalso. clear - H0 H1 e. subst. apply H1. 
        rewrite name_member_get. auto.
        auto.
Qed.

Lemma struct_pred_upd: forall m {A} (P: forall it, A it -> val -> mpred) (i: ident) v p v0,
  let P' it := if ident_eq i (name_member it) then fun _ _ => emp else P it in
  members_no_replicate m = true ->
  in_members i m ->
  struct_pred m P (upd_struct i m v v0) p = (P _ v0 p ∗ struct_pred m P' v p).
Proof.
  intros.
  destruct m as [| a0 m]; [inv H0 |].
  unfold proj_struct, field_type in *.
  revert a0 H v v0 H0; induction m as [| a1 m]; intros.
  + subst P'; simpl in *.
    destruct H0; [simpl in H0; subst i | tauto].
    destruct (ident_eq _ _); [| congruence].
    destruct (member_dec a0 a0); [| congruence].
    unfold eq_rect_r; rewrite <- eq_rect_eq.
    rewrite sep_emp; auto.
  + pose proof H.
    apply members_no_replicate_ind in H1; destruct H1.
    simpl compact_prod in v |- *; simpl Ctypes.field_type in v0 |- *.
    set (v' := (upd_struct i (a0 :: a1 :: m) v v0)).
    change (struct_pred (a0 :: a1 :: m) P v' p)
      with (P _ (fst v') p ∗ struct_pred (a1 :: m) P (snd v') p).
    change (struct_pred (a0 :: a1 :: m) P' v p)
      with (P' _ (fst v) p ∗ struct_pred (a1 :: m) P' (snd v) p).
    subst v'.
    unfold upd_struct.
    change (get_member i (a0::a1::m)) with
       (if ident_eq i (name_member a0) then a0 else get_member i (a1::m))
       in v0|-*.
    destruct (ident_eq i _).
    - subst i.
      simpl.
      destruct (member_dec a0 a0); [| congruence].
      f_equal.
      * simpl.
        unfold eq_rect_r; rewrite <- eq_rect_eq.
        auto.
      * simpl.
        unfold eq_rect_r; rewrite <- eq_rect_eq.
        change (snd (v0, snd v)) with (snd v).
        change (struct_pred (a1 :: m) P (snd v) p = (P' a0 (fst v) p ∗ struct_pred (a1 :: m) P' (snd v) p)).
        erewrite struct_pred_not_member by eauto.
        unfold P' at 1.
        rewrite -> if_true by auto.
        rewrite emp_sep; auto.
    - destruct H0; [simpl in H0; congruence |].
      rewrite sep_assoc (sep_comm _ (P' _ _ _)) -sep_assoc.
      simpl.
      destruct (member_dec _ _).
      change (get_member i (a1::m) = a0) in e.
      exfalso; clear - e H0 H1. subst. apply H1. rewrite name_member_get. auto.
      f_equal.
      * unfold P'; simpl.
        rewrite -> if_false by (simpl; congruence).
        auto.
      * simpl snd.
        simpl in IHm |- *; erewrite IHm by auto.
        reflexivity.
Qed.

Lemma struct_pred_ramif: forall m {A} (P: forall it, A it -> val -> mpred) (i: ident) v p d,
  in_members i m ->
  members_no_replicate m = true ->
  struct_pred m P v p ⊢
    P _ (proj_struct i m v d) p ∗
     (∀ v0: _, P _ v0 p -∗ struct_pred m P (upd_struct i m v v0) p).
Proof.
  intros.
  set (P' it := if ident_eq i (name_member it) then fun _ _ => emp else P it).
  erewrite struct_pred_proj by done.
  iIntros "($ & ?)" (?) "?".
  rewrite struct_pred_upd //.
  iFrame.
Qed.

Lemma at_offset_struct_pred: forall m {A} (P: forall it, A it -> val -> mpred) v p ofs,
  at_offset (struct_pred m P v) ofs p = struct_pred m (fun it v => at_offset (P it v) ofs) v p.
Proof.
  intros.
  rewrite at_offset_eq.
  destruct m as [| a0 m]; [auto |].
  revert a0 v; induction m as [| a1 m]; intros.
  + simpl.
    rewrite at_offset_eq //.
  + simpl.
    rewrite at_offset_eq //.
Qed.

Lemma corable_andp_struct_pred: forall m {A} (P: forall it, A it -> val -> mpred) v p Q {_ : Persistent Q} {_ : Absorbing Q},
  Q ∧ struct_pred m P v p ⊣⊢
  match m with
  | nil => Q ∧ emp
  | _ => struct_pred m (fun it v p => Q ∧ P it v p) v p
  end.
Proof.
  intros.
  destruct m as [| a0 m]; [auto |].
  revert a0 v; induction m as [| a1 m]; intros.
  + simpl.
    auto.
  + change (struct_pred (a0::a1::m) P v p)
      with (P a0 (fst v) p ∗ struct_pred (a1 :: m) P (snd v) p).
    iSplit.
    * iIntros "(#? & P & ?)".
      iSplitL "P"; first by iSplit.
      setoid_rewrite <- IHm; by iSplit.
    * iIntros "((? & $) & ?)".
      setoid_rewrite <- IHm; auto.
Qed.

Lemma struct_pred_sepcon: forall m {A} (P Q: forall it, A it -> val -> mpred) v p,
  (struct_pred m P v p ∗ struct_pred m Q v p) = struct_pred m (fun it a v => P it a v ∗ Q it a v) v p.
Proof.
  intros.
  destruct m as [| a0 m]; [| revert a0 v; induction m as [| a1 m]; intros].
  + simpl.
    rewrite emp_sep; auto.
  + simpl.
    auto.
  + change (struct_pred (a0 :: a1 :: m) P v p)
      with (P a0 (fst v) p ∗ struct_pred (a1 :: m) P (snd v) p).
    change (struct_pred (a0 :: a1 :: m) Q v p)
      with (Q a0 (fst v) p ∗ struct_pred (a1 :: m) Q (snd v) p).
    change (struct_pred (a0 :: a1 :: m) (fun it a v => P it a v ∗ Q it a v) v p)
      with ((P a0 (fst v) p ∗ Q a0 (fst v) p) ∗ struct_pred (a1 :: m) (fun it a v => P it a v ∗ Q it a v) (snd v) p).
    rewrite -!sep_assoc; f_equiv.
    rewrite sep_assoc (sep_comm _ (Q _ _ _)) -sep_assoc; f_equal; first done.
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
  + done.
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
  (forall i (Hin: in_members i m) d0 d1, members_union_inj v0 (get_member i m) -> members_union_inj v1 (get_member i m) ->
     P0 _ (proj_union i m v0 d0) p ⊢ P1 _ (proj_union i m v1 d1) p) ->
  union_pred m P0 v0 p ⊢ union_pred m P1 v1 p.
Proof.
  unfold members_union_inj, proj_union, field_type.
  intros.
  destruct m as [| a0 m]; [simpl; auto |].
  revert a0 v0 v1 H H0 H1; induction m as [| a1 m]; intros.
  + specialize (H1 (name_member a0)).
    simpl in H1.
    if_tac in H1; [| congruence].
   spec H1. left; auto.
    specialize (H1 v0 v1).
    spec H1; [if_tac; [auto | congruence] |].
    spec H1; [if_tac; [auto | congruence] |].
    destruct (member_dec a0 a0); [| congruence].
    unfold eq_rect_r in H1; rewrite <- !eq_rect_eq in H1.
    simpl.
    exact H1.
  + rewrite compact_sum_inj_eq_spec in H0.
    2:{
      clear - H. unfold members_no_replicate in H. apply compute_list_norepet_e in H. inv H.
      contradict H2. apply in_map with (f := name_member) in H2. auto.
    }
    destruct v0 as [v0 | v0], v1 as [v1 | v1]; try solve [inversion H0].
    - specialize (H1 (name_member a0)).
      simpl in H1.
      if_tac in H1; [| congruence].
   spec H1. left; auto.
      specialize (H1 v0 v1).
      spec H1; [if_tac; [auto | congruence] |].
      spec H1; [if_tac; [auto | congruence] |].
      destruct (member_dec a0 a0); [| congruence].
      unfold eq_rect_r in H1; rewrite <- !eq_rect_eq in H1.
      simpl.
      exact H1.
    - rewrite members_no_replicate_ind in H.
      apply IHm; [tauto | tauto |].
      intros.
      specialize (H1 i).
      change (get_member i (a0::a1::m)) with
           (if ident_eq i (name_member a0) then a0 else get_member i (a1::m)) in *.
      if_tac in H1. (* i = i0 vs i <> i0 *)
      * clear - H H2 H4.
        pose proof compact_sum_inj_in v0 (get_member i (a1 :: m)) member_dec.
        spec H0; [exact H2 |].
        subst.
        apply in_map with (f := name_member) in H0.
        rewrite name_member_get in H0.
        tauto.
      * spec H1.
         right; auto.
         specialize (H1 d0 d1).
         unfold compact_sum_inj, proj_compact_sum, list_rect in H1.
        destruct (member_dec (get_member i (a1::m)) a0).
        exfalso. clear - e H4. subst. rewrite name_member_get in H4. congruence.
        apply (H1 H2 H3).
Qed.

Lemma union_pred_ext: forall m {A0 A1} (P0: forall it, A0 it -> val -> mpred) (P1: forall it, A1 it -> val -> mpred) v0 v1 p,
  members_no_replicate m = true ->
  (forall it, members_union_inj v0 it <-> members_union_inj v1 it) ->
  (forall i (Hin: in_members i m) d0 d1, members_union_inj v0 (get_member i m) -> members_union_inj v1 (get_member i m) ->
     P0 _ (proj_union i m v0 d0) p ⊣⊢ P1 _ (proj_union i m v1 d1) p) ->
  union_pred m P0 v0 p ⊣⊢ union_pred m P1 v1 p.
Proof.
  intros.
  assert (forall it, members_union_inj v1 it <-> members_union_inj v0 it)
    by (intro it; specialize (H0 it); tauto).
  iSplit; iApply union_pred_ext_derives; auto;
  intros; erewrite H1 by eauto; apply derives_refl.
Qed.

Lemma union_pred_derives_const: forall m {A} (P: forall it, A it -> val -> mpred) p v R,
  members_no_replicate m = true ->
  m <> nil ->
  (forall i (v: A (get_member i m)), in_members i m -> P _ v p ⊢ R) ->
  union_pred m P v p ⊢ R.
Proof.
  intros.
  destruct m as [| a0 m]; [congruence |].
  clear H0.
  revert a0 v H H1; induction m as [| a1 m]; intros.
  + simpl.
    specialize (H1 (name_member a0)); simpl in H1.
    destruct (ident_eq (name_member a0) (name_member a0)); [| congruence].
    apply H1; left; auto.
  + destruct v; simpl.
    - specialize (H1 (name_member a0)); simpl in H1.
      destruct (ident_eq (name_member a0) (name_member a0)); [| congruence].
      apply H1; left; auto.
    - pose proof H.
      rewrite members_no_replicate_ind in H; destruct H.
      apply (IHm a1); auto.
      intros.
      specialize (H1 i).
     change (get_member i (a0::a1::m)) with (if ident_eq i (name_member a0) then a0 else get_member i (a1::m)) in *.
      destruct (ident_eq i (name_member a0)).
      exfalso; clear - H0 H3 e. subst. unfold members_no_replicate in H0. apply compute_list_norepet_e in H0. inv H0.
      apply H2. apply H3. 
      apply H1.
      right; auto.
Qed.

Lemma union_pred_proj: forall m {A} (P: forall it, A it -> val -> mpred) (i: ident) v p d,
  members_no_replicate m = true ->
  in_members i m ->
  (forall i' (v': A (get_member i' m)), in_members i' m -> P _ v' p ⊢ P _ d p) ->
  union_pred m P v p ⊢ P _ (proj_union i m v d) p.
Proof.
  intros.
  destruct m as [| a0 m]; [inv H0 |].
  revert a0 v d H H0 H1; induction m as [| a1 m]; intros.
  + destruct H0; [simpl in H0; subst i | tauto].
    simpl in *.
    destruct (ident_eq _ _ ); [| congruence].
    destruct (member_dec a0 a0); [| congruence].
    unfold eq_rect_r; rewrite <- eq_rect_eq.
    auto.
  + pose proof H.
    rewrite members_no_replicate_ind in H; destruct H.
     change (get_member i (a0::a1::m)) with (if ident_eq i (name_member a0) then a0 else get_member i (a1::m)) in *.
     simpl proj_union.
     destruct (ident_eq i (name_member a0)).
    - subst i.
      destruct (member_dec a0 a0); [| congruence].
      unfold eq_rect_r; rewrite <- eq_rect_eq.
      destruct v; auto.
      simpl. auto.
      apply (union_pred_derives_const (a1 :: m)); [auto | congruence |].
      intros.
      specialize (H1 i).
      change (get_member i (a0::a1::m)) with (if ident_eq i (name_member a0) then a0 else get_member i (a1::m)) in *.
      rewrite if_false in H1. apply H1.
      right; auto. 
      clear - H4 H2. apply compute_list_norepet_e in H2. inv H2.
      contradict H1. subst; auto. 
    - change (if ident_eq i (name_member a1) then a1 else get_member i m) with (get_member i (a1::m)) in *.
       destruct (member_dec _ _).
       exfalso; clear - n e. subst.
       rewrite -> name_member_get in *. congruence.
       destruct v.
       unfold union_pred. unfold list_rect.
       specialize (H1 (name_member a0)). 
        simpl get_member in H1.
       rewrite -> if_true in H1 by auto. apply H1. left. auto.
      apply IHm; auto. destruct H0; auto.  congruence.
       intros.
        specialize (H1 i').
        simpl in H1. rewrite if_false in H1.
        apply H1. right; auto.
        clear - H2 H4. intro; subst. apply compute_list_norepet_e in H2. inv H2.
        apply H1. auto.
Qed.

Lemma union_pred_upd: forall m {A} (P: forall it, A it -> val -> mpred) (i: ident) v p v0,
  members_no_replicate m = true ->
  in_members i m ->
  union_pred m P (upd_union i m v v0) p = P _ v0 p.
Proof.
  intros.
  intros.
  unfold upd_union, upd_compact_sum.
  destruct (in_dec member_dec (get_member i m) m) as [?H | ?H];
   [ | contradiction H1; apply in_get_member; auto].
  clear v.
  destruct m as [| a0 m]; [inv H0 |].
  revert a0 v0 H H0 H1; induction m as [| a1 m]; intros.
  + simpl in *.
    destruct H0; [simpl in H0; subst i | tauto].
    destruct (ident_eq _ _); [| congruence].
    destruct (member_dec a0 a0); [| congruence].
    unfold eq_rect_r; rewrite <- eq_rect_eq.
    auto.
  + destruct H0; [simpl in H0; subst i |].
    - simpl in *.
      destruct (ident_eq _ _); [| congruence].
      destruct (member_dec a0 a0); [| congruence].
      unfold eq_rect_r; rewrite <- eq_rect_eq.
      auto.
    -
       change (get_member i (a0::a1::m)) with (if ident_eq i (name_member a0) then a0 else get_member i (a1::m)) in *.
      destruct (ident_eq _ _).
      exfalso; clear - e H H0 H1. subst.
      apply compute_list_norepet_e in H. inv H. apply H4.
      destruct H0. left; auto. right; auto.
      unfold union_pred. unfold list_rect.
      destruct (member_dec _ _).
      exfalso.
      clear - H H0 H1 e. forget (a1::m) as m1. subst a0. 
      apply compute_list_norepet_e in H. inv H. rewrite name_member_get in H4. contradiction.
      apply (IHm a1); auto.
      apply members_no_replicate_ind in H. tauto.
Qed.

Lemma union_pred_ramif: forall m {A} (P: forall it, A it -> val -> mpred) (i: ident) v p d,
  (forall i' (v': A (get_member i' m)), in_members i' m -> P _ v' p ⊢ P _ d p) ->
  in_members i m ->
  members_no_replicate m = true ->
  union_pred m P v p ⊢
    P _ (proj_union i m v d) p ∗
     (∀ v0: _, P _ v0 p -∗ union_pred m P (upd_union i m v v0) p).
Proof.
  intros.
  rewrite union_pred_proj //.
  iIntros "$" (?) "?".
  rewrite union_pred_upd //.
Qed.

Lemma at_offset_union_pred: forall m {A} (P: forall it, A it -> val -> mpred) v p ofs,
  at_offset (union_pred m P v) ofs p = union_pred m (fun it v => at_offset (P it v) ofs) v p.
Proof.
  intros.
  rewrite at_offset_eq.
  destruct m as [| a0 m]; [simpl; auto |].
  revert a0 v; induction m as [| a1 m]; intros.
  + simpl.
    rewrite at_offset_eq.
    auto.
  + simpl.
    destruct v.
    - rewrite at_offset_eq.
      auto.
    - apply IHm.
Qed.

Lemma andp_union_pred: forall m {A} (P: forall it, A it -> val -> mpred) v p Q,
  (Q ∧ union_pred m P v p) =
  match m with
  | nil => Q ∧ emp
  | _ => union_pred m (fun it v p => Q ∧ P it v p) v p
  end.
Proof.
  intros.
  destruct m as [| a0 m]; [auto |].
  revert a0 v; induction m as [| a1 m]; intros.
  + simpl.
    auto.
  + destruct v.
    - simpl.
      auto.
    - simpl.
      apply IHm.
Qed.

Lemma union_pred_sepcon: forall m {A} (P Q: forall it, A it -> val -> mpred) v p,
  (union_pred m P v p ∗ union_pred m Q v p) = union_pred m (fun it v p => P it v p ∗ Q it v p) v p.
Proof.
  intros.
  destruct m as [| a0 m]; [| revert a0 v; induction m as [| a1 m]; intros].
  + simpl.
    rewrite sep_emp //.
  + simpl.
    auto.
  + destruct v.
    - simpl; auto.
    - apply IHm.
Qed.

Lemma struct_Prop_compact_prod_gen: forall m (F: member -> Type) (P: forall it, F it -> Prop) (f: forall it, F it),
  members_no_replicate m = true ->
  (forall i, in_members i m -> P (get_member i m) (f (get_member i m))) ->
  struct_Prop m P (compact_prod_gen f m).
Proof.
  intros.
  destruct m as [| a0 m]; [simpl; auto |].
  revert a0 H H0; induction m as [| a1 m]; intros.
  + simpl.
    specialize (H0 (name_member a0)).
    simpl in H0.
    rewrite -> if_true in H0 by auto.
    apply H0; left; auto.
  + change (struct_Prop (a0 :: a1 :: m) P
             (compact_prod_gen f (a0 :: a1 :: m)))
    with (P a0 (f a0) /\
            struct_Prop (a1 :: m) P (compact_prod_gen f (a1 :: m))).
    split.
    - specialize (H0 (name_member a0)).
      simpl in H0.
      rewrite -> if_true in H0 by auto.
      apply H0; left; auto.
    - rewrite members_no_replicate_ind in H; destruct H.
      apply (IHm a1); auto.
      intros.
      specialize (H0 i).
      simpl in H0.
      destruct (ident_eq i (name_member a0)); [subst; tauto |].
      apply H0; right; auto.
Qed.

Lemma struct_Prop_proj: forall m (F: member -> Type) (P: forall it, F it -> Prop) v i d,
  in_members i m ->
  struct_Prop m P v ->
  P (get_member i m) (proj_struct i m v d).
Proof.
  intros.
  destruct m as [| a0 m]; [inversion H |].
  revert a0 v d H H0; induction m as [| a1 m]; intros.
  + inversion H; [simpl in H0; subst| tauto].
    simpl in *.
    destruct (ident_eq _ _); [| tauto].
    destruct (member_dec a0 a0); [| tauto].
    unfold eq_rect_r; rewrite <- eq_rect_eq.
    auto.
  + destruct (ident_eq i (name_member a0)).
    - subst.
      simpl in *.
      destruct (ident_eq _ _ ); [| tauto].
      destruct (member_dec a0 a0); [| tauto].
      unfold eq_rect_r; rewrite <- eq_rect_eq.
      exact (proj1 H0).
    - assert (in_members i (a1 :: m)) by (inversion H; [subst; tauto | auto]).
      simpl in *.
      destruct (ident_eq _ _); [tauto |].
      destruct (member_dec _ _).
      exfalso; clear - e n.
      change (if  ident_eq i (name_member a1) then a1 else get_member i m) 
       with (get_member i (a1::m))  in e. subst. rewrite name_member_get in n. contradiction.
      apply IHm; auto.
      exact (proj2 H0).
Qed.

Lemma union_Prop_compact_sum_gen: forall m (F: member -> Type) (P: forall it, F it -> Prop) (f: forall it, F it),
  members_no_replicate m = true ->
  (forall i, in_members i m -> P (get_member i m) (f (get_member i m))) ->
  union_Prop m P (compact_sum_gen (fun _ => true) f m).
Proof.
  intros.
  destruct m as [| a0 m]; [simpl; auto |].
  destruct m as [| a1 m].
  + simpl.
    specialize (H0 (name_member a0)).
    simpl in H0.
    rewrite -> if_true in H0 by auto.
    apply H0; left; auto.
  + simpl.
    specialize (H0 (name_member a0)).
    simpl in H0.
    rewrite -> if_true in H0 by auto.
    apply H0; left; auto.
Qed.

Lemma union_Prop_proj: forall m (F: member -> Type) (P: forall it, F it -> Prop) v i d,
  members_union_inj v (get_member i m) ->
  union_Prop m P v ->
  P (get_member i m) (proj_union i m v d).
Proof.
  intros.
  destruct m as [| a0 m]; [inversion H |].
  revert a0 v d H H0; induction m as [| a1 m]; intros.
  + simpl in H. simpl proj_union.
    unfold eq_rect_r.
     if_tac in H; [| tauto].
    change (if ident_eq i (name_member a0) then a0 else Member_plain i Tvoid) with
              (get_member i (a0::nil)) in *.
    simpl in H0.
    destruct a0; simpl in *.
   if_tac.  rewrite <- eq_rect_eq; auto.
   unfold eq_rect. destruct H1. simpl. auto.
   if_tac.  rewrite <- eq_rect_eq; auto.
   unfold eq_rect. destruct H1. simpl. auto.
  + 
    unfold proj_union. 
    change (get_member i (a0::a1::m)) with (if ident_eq i (name_member a0) then a0 else get_member i (a1::m)) in *.
    if_tac. 
    - subst.
     simpl. 
      simpl in H.
      destruct (member_dec a0 a0); [| tauto].
      unfold eq_rect_r; rewrite <- eq_rect_eq.
      destruct v; [| inversion H].
      auto.
    - assert (members_union_inj v (get_member i (a1 :: m))) 
       by (simpl in H; destruct (ident_eq i (name_member a0)); [tauto | auto]).
      set (j := get_member i (a1::m)) in *.
      simpl in H|-*.
      destruct (member_dec _ _).
      subst a0.
      exfalso; clear - j H1. subst j. rewrite name_member_get in H1. contradiction.
      destruct v; [ tauto | ]. 
      apply IHm; auto.
Qed.

Lemma array_pred_local_facts: forall {A}{d: Inhabitant A} lo hi P (v: list A) p Q,
  (forall i x, lo <= i < hi -> P i x p ⊢ ⌜Q x⌝) ->
  array_pred lo hi P v p ⊢ ⌜Zlength v = hi - lo /\ Forall Q v⌝.
Proof.
  intros.
  unfold array_pred.
  iIntros "(% & H)"; iSplit; first done.
  pose proof ZtoNat_Zlength v.
  rewrite H0 in H1; symmetry in H1; clear H0.
  iInduction v as [|] "IH" forall (hi lo H H1); intros.
  + done.
  + replace (hi - lo) with (Z.succ (hi - Z.succ lo)) in * by lia.
    assert (hi - Z.succ lo >= 0).
    {
      destruct (zlt (hi - Z.succ lo) 0); auto.
      assert (Z.succ (hi - Z.succ lo) <= 0) by lia.
      simpl length in H1.
      destruct (zeq (Z.succ (hi - Z.succ lo)) 0);
       [rewrite e in H1 | rewrite -> Z2Nat_neg in H1 by lia]; inv H1.
    }
    rewrite  ->Z2Nat.inj_succ in H1 |- * by lia.
    inv H1.
    simpl rangespec.
    erewrite rangespec_ext with (P' := fun i : Z => P i (Znth (i - Z.succ lo) v)).
    2:{
      intros.
      change v with (skipn 1 (a :: v)) at 1.
      rewrite -> Znth_succ by lia.
      auto.
    }
    iDestruct "H" as "(P & H)".
    rewrite H3; iDestruct ("IH" with "[%] [%] H") as %?; try done.
    - intros; apply H; lia.
    - rewrite H; last lia.
      iDestruct "P" as %Ha; iPureIntro; constructor; auto.
      rewrite Z.sub_diag // in Ha.
Qed.

Lemma struct_pred_local_facts: forall m {A} (P: forall it, A it -> val -> mpred)v p (R: forall it, A it -> Prop),
  members_no_replicate m = true ->
  (forall i v0, in_members i m -> P (get_member i m) v0 p ⊢ ⌜R _ v0⌝) ->
  struct_pred m P v p ⊢ ⌜struct_Prop m R v⌝.
Proof.
  intros.
  destruct m as [| a0 m]; [by iIntros "_" |].
  revert a0 v H H0; induction m as [| a1 m]; intros.
  + simpl.
    specialize (H0 (name_member a0)).
    simpl in H0.
    rewrite -> if_true in H0 by auto.
    apply H0; left; auto.
  + change (struct_Prop (a0 :: a1 :: m) R v)
      with (R a0 (fst v) /\ struct_Prop (a1 :: m) R (snd v)).
    change (struct_pred (a0 :: a1 :: m) P v p)
      with (P a0 (fst v) p ∗ struct_pred (a1 :: m) P (snd v) p).
    rewrite members_no_replicate_ind in H.

    pose proof H0 (name_member a0).
    simpl in H1.
    if_tac in H1; [| congruence].
    specialize (H1 (fst v)).
    spec H1; [left; auto |].

    specialize (IHm a1 (snd v)).
    spec IHm; [tauto |].
    rewrite H1 IHm.
    - iIntros "(% & %)"; iPureIntro; constructor; auto.
    - intros.
      specialize (H0 i).
      simpl in H0.
      destruct (ident_eq i (name_member a0)); [subst; tauto |].
      apply H0; right; auto.
Qed.

Lemma union_pred_local_facts: forall m {A} (P: forall it, A it -> val -> mpred)v p (R: forall it, A it -> Prop),
  members_no_replicate m = true ->
  (forall i v0, in_members i m -> P (get_member i m) v0 p ⊢ ⌜R _ v0⌝) ->
  union_pred m P v p ⊢ ⌜union_Prop m R v⌝.
Proof.
  intros.
  destruct m as [| a0 m]; [by iIntros "_" |].
  revert a0 v H H0; induction m as [| a1 m]; intros.
  + simpl.
    specialize (H0 (name_member a0)).
    simpl in H0.
    rewrite -> if_true in H0 by auto.
    apply H0; left; auto.
  + rewrite members_no_replicate_ind in H.
    destruct v.
    - simpl.
      pose proof H0 (name_member a0).
      simpl in H1.
      if_tac in H1; [| congruence].
      specialize (H1 a).
      apply H1; left; auto.
    - specialize (IHm a1 c).
      spec IHm; [tauto |].
      apply IHm.
      intros.
      specialize (H0 i).
      simpl in H0.
      destruct (ident_eq i (name_member a0)); [subst; tauto |].
      apply H0; right; auto.
Qed.

Section MEMORY_BLOCK_AGGREGATE.

Context {cs: compspecs}.

Lemma memory_block_array_pred: forall  {A}{d: Inhabitant A} sh t lo hi (v: list A) b ofs,
  0 <= ofs + sizeof t * lo /\ ofs + sizeof t * hi < Ptrofs.modulus ->
  0 <= lo <= hi ->
  Zlength v = hi - lo ->
  array_pred lo hi
    (fun i _ p => memory_block sh (sizeof t) (offset_val (sizeof t * i) p)) v
    (Vptr b (Ptrofs.repr ofs)) ⊣⊢
   memory_block sh (sizeof t * (hi - lo)) (Vptr b (Ptrofs.repr (ofs + sizeof t * lo))).
Proof.
  intros.
  unfold array_pred.
  rewrite -> prop_true_andp by auto; clear H1.
  f_equal.
  remember (Z.to_nat (hi - lo)) as n eqn:HH.
  revert lo HH H H0 v; induction n; intros.
  + simpl.
    pose proof arith_aux00 _ _ (proj2 H0) HH.
    rewrite H1 Z.mul_0_r memory_block_zero_Vptr //.
  + simpl.
    pose proof arith_aux01 _ _ _ HH.
    solve_mod_modulus.
    pose_size_mult cs t (0 :: hi - Z.succ lo :: hi - lo :: nil).
    rewrite IHn; [| apply arith_aux02; auto | lia | lia | exact v].
    replace (ofs + sizeof  t * Z.succ lo) with (ofs + sizeof t * lo + sizeof t) by lia.
    rewrite <- memory_block_split by (auto; lia).
    f_equiv; hnf; lia.
Qed.

Lemma mapsto_zeros_zero_Vptr
     : forall (sh : share) (b : block) (z : ptrofs),
       mapsto_zeros 0 sh (Vptr b z) = emp.
Proof.
intros.
unfold mapsto_zeros. simpl.
rewrite prop_true_andp //.
rep_lia.
Qed.

Lemma mapsto_zeros_split
     : forall (sh : share) (b : block) (ofs n m : Z),
       0 <= n ->
       0 <= m ->
       n + m <= n + m + ofs < Ptrofs.modulus ->
       mapsto_zeros (n + m) sh (Vptr b (Ptrofs.repr ofs)) ⊣⊢
       mapsto_zeros n sh (Vptr b (Ptrofs.repr ofs)) ∗
       mapsto_zeros m sh (Vptr b (Ptrofs.repr (ofs + n))).
Proof.
intros.
unfold mapsto_zeros.
rewrite -> !Ptrofs.unsigned_repr by rep_lia.
rewrite -> !prop_true_andp by rep_lia.
rewrite !mapsto_memory_block.address_mapsto_zeros_eq.
rewrite -> !Z2Nat.id by lia.
apply mapsto_memory_block.address_mapsto_zeros'_split; lia.
Qed.

Lemma mapsto_zeros_array_pred: forall  {A}{d: Inhabitant A} sh t lo hi (v: list A) b ofs,
  0 <= ofs + sizeof t * lo /\ ofs + sizeof t * hi < Ptrofs.modulus ->
  0 <= lo <= hi ->
  Zlength v = hi - lo ->
   mapsto_zeros (sizeof t * (hi - lo)) sh (Vptr b (Ptrofs.repr (ofs + sizeof t * lo))) ⊢
  array_pred lo hi
    (fun i _ p => mapsto_zeros (sizeof t) sh (offset_val (sizeof t * i) p)) v
    (Vptr b (Ptrofs.repr ofs)).
Proof.
  intros.
  unfold array_pred.
Opaque mapsto_zeros.
  rewrite -> prop_true_andp by auto; clear H1.
  f_equal.
  remember (Z.to_nat (hi - lo)) as n eqn:HH.
  revert lo HH H H0 v; induction n; intros.
  +  simpl. 
    pose proof arith_aux00 _ _ (proj2 H0) HH.
    rewrite H1 Z.mul_0_r mapsto_zeros_zero_Vptr //.
  + simpl.
    pose proof arith_aux01 _ _ _ HH.
    solve_mod_modulus.
    pose_size_mult cs t (0 :: hi - Z.succ lo :: hi - lo :: nil).
    rewrite -IHn //; [| lia..].
    replace (ofs + sizeof  t * Z.succ lo) with (ofs + sizeof t * lo + sizeof t) by lia.
    rewrite <- mapsto_zeros_split by (auto; lia).
    apply bi.equiv_entails_1_1; f_equiv; hnf; lia.
Transparent mapsto_zeros.
Qed.

Lemma memory_block_array_pred': forall {A}{d: Inhabitant A} (a: A) sh t z b ofs,
  0 <= z ->
  0 <= ofs /\ ofs + sizeof t * z < Ptrofs.modulus ->
  array_pred 0 z
     (fun i _ p =>
      memory_block sh (sizeof t) (offset_val (sizeof t * i) p))
             (Zrepeat a z)
     (Vptr b (Ptrofs.repr ofs)) ⊣⊢
  memory_block sh (sizeof t * z) (Vptr b (Ptrofs.repr ofs)).
Proof.
  intros.
  rewrite memory_block_array_pred //.
  f_equiv; hnf; first lia. do 2 f_equal; lia.
  lia.
  rewrite Z.sub_0_r. rewrite -> Zlength_Zrepeat by lia.
  done.
Qed.

Lemma mapsto_zeros_array_pred': forall {A}{d: Inhabitant A} (a: A) sh t z b ofs,
  0 <= z ->
  0 <= ofs /\ ofs + sizeof t * z < Ptrofs.modulus ->
  mapsto_zeros (sizeof t * z) sh (Vptr b (Ptrofs.repr ofs)) ⊢
  array_pred 0 z
     (fun i _ p =>
      mapsto_zeros (sizeof t) sh(offset_val (sizeof t * i) p))
             (Zrepeat a z)
     (Vptr b (Ptrofs.repr ofs)).
Proof.
  intros.
  rewrite -mapsto_zeros_array_pred //; [|try lia..].
  apply bi.equiv_entails_1_1; f_equiv; hnf; first lia. do 2 f_equal; lia.
  rewrite -> Zlength_Zrepeat by lia.
  lia.
Qed.

Lemma memory_block_struct_pred: forall sh m sz {A} (v: compact_prod (map A m)) b ofs,
  (m = nil -> sz = 0) ->
  plain_members m = true ->
  members_no_replicate m = true ->
  sizeof_struct cenv_cs 0 m <= sz < Ptrofs.modulus ->
  0 <= ofs /\ ofs + sz < Ptrofs.modulus ->
  struct_pred m
   (fun it _ p =>
     (memory_block sh (field_offset_next cenv_cs (name_member it) m sz - field_offset cenv_cs (name_member it) m))
     (offset_val (field_offset cenv_cs (name_member it) m) p)) v (Vptr b (Ptrofs.repr ofs)) ⊣⊢
  memory_block sh sz (Vptr b (Ptrofs.repr ofs)).
Proof.
  unfold field_offset, Ctypes.field_offset, field_offset_next.
  intros sh m sz A v b ofs NIL_CASE PLAIN NO_REPLI; intros.
  destruct m as [| a0 m].
  1: rewrite (NIL_CASE eq_refl) memory_block_zero; simpl; normalize.
  pose (t0 := type_member a0).
  assert (align 0 (alignof t0) = 0) by apply align_0, alignof_pos.
  revert H0; pattern ofs at 1 4; replace ofs with (ofs + align 0 (alignof t0)) by lia; intros.
  revert H; pattern sz at 2 4; replace sz with (sz - align 0 (alignof t0)) by lia; intros.
  pattern 0 at 1; rewrite <- H1.
  clear NIL_CASE H1.
  destruct a0; try discriminate. simpl in t0. subst t0. simpl in PLAIN.
  rename id into i0. rename t into t0. 
  revert H H0. generalize 0 at 1 2 4 5 6 7 8 9; revert i0 t0 v PLAIN NO_REPLI;
  induction m as [| a1 m]; intros.
  + simpl.
    if_tac; [| congruence].
    solve_mod_modulus.
    reflexivity.
  + match goal with
    | |- struct_pred (Member_plain i0 t0 :: a1 :: m) ?P v ?p ⊣⊢ _ =>
           change (struct_pred (Member_plain i0 t0 :: a1 :: m) P v p) with
             (P (Member_plain i0 t0) (fst v) p ∗ struct_pred (a1 :: m) P (snd v) p);
           simpl (P (Member_plain i0 t0) (fst v) p)
    end.
    if_tac; [| congruence].
    solve_mod_modulus.
    destruct a1 as [i1 t1|]; try discriminate.
   destruct v as [v0 v1].
   rewrite members_no_replicate_ind in NO_REPLI; destruct NO_REPLI as [NOT_IN NO_REPLI].
    specialize (IHm i1 t1 v1 PLAIN NO_REPLI (align z (alignof t0) + sizeof t0)).
    simpl snd.
    fold (sizeof t0) in *. fold (alignof t0) in *.
    erewrite struct_pred_ext.
    - erewrite IHm;
        [| simpl in H |- *; 
          fold (sizeof t0) in *; fold (alignof t0) in *;
          fold (sizeof t1) in *; fold (alignof t1) in *;
          pose_align_le; pose_sizeof_pos; lia
         | pose_align_le; pose_sizeof_pos; lia].
      replace (ofs + align (align z (alignof t0) + sizeof t0) (alignof t1)) with
        (ofs + align z (alignof t0) +
         (align (align z (alignof t0) + sizeof t0) (alignof t1) -
          align z (alignof t0))) by lia.
      simpl; fold (alignof t1).
      rewrite <- memory_block_split by (simpl in H;
          fold (sizeof t0) in *; fold (alignof t0) in *;
          fold (sizeof t1) in *; fold (alignof t1) in *; revert H; pose_align_le; pose_sizeof_pos; intros; unfold align in *; lia).
      f_equiv; hnf. lia.
    - auto.
    - intros.
      solve_mod_modulus.
      unfold fst.
      rewrite !name_member_get.
      assert (i <> name_member (Member_plain i0 t0)).
      simpl. clear - H2 NOT_IN.  contradict NOT_IN. subst i0. simpl. auto.
      rewrite -> (neq_field_offset_rec_cons cenv_cs i (Member_plain i0 t0)) by auto.
      rewrite -> (neq_field_offset_next_rec_cons cenv_cs i (Member_plain i0 t0)) by  auto.
      reflexivity.
Qed.

Lemma mapsto_zeros_zero: forall (sh : share) (p : val), 
   mapsto_zeros 0 sh p = (⌜isptr p⌝ ∧ emp).
Proof.
intros.
unfold mapsto_zeros; simpl. destruct p; simpl; rewrite ?log_normalize.False_and //.
rewrite -> prop_true_andp by rep_lia.
rewrite log_normalize.True_and //.
Qed.

Lemma mapsto_zeros_struct_pred: forall sh m sz {A} (v: compact_prod (map A m)) b ofs,
  (m = nil -> sz = 0) ->
  plain_members m = true ->
  members_no_replicate m = true ->
  sizeof_struct cenv_cs 0 m <= sz < Ptrofs.modulus ->
  0 <= ofs /\ ofs + sz < Ptrofs.modulus ->
  mapsto_zeros sz sh (Vptr b (Ptrofs.repr ofs)) ⊢
  struct_pred m
   (fun it _ p =>
     (mapsto_zeros (field_offset_next cenv_cs (name_member it) m sz - field_offset cenv_cs (name_member it) m)) sh
     (offset_val (field_offset cenv_cs (name_member it) m) p)) v (Vptr b (Ptrofs.repr ofs)).
Proof.
  Opaque mapsto_zeros.
  unfold field_offset, Ctypes.field_offset, field_offset_next.
  intros sh m sz A v b ofs NIL_CASE PLAIN NO_REPLI; intros.
  destruct m as [| a0 m].
  1: rewrite (NIL_CASE eq_refl) mapsto_zeros_zero; simpl; normalize.
  pose (t0 := type_member a0).
  assert (align 0 (alignof t0) = 0) by apply align_0, alignof_pos.
  revert H0; pattern ofs at 1 3; replace ofs with (ofs + align 0 (alignof t0)) by lia; intros.
  revert H; pattern sz at 2 3; replace sz with (sz - align 0 (alignof t0)) by lia; intros.
  pattern 0 at 3; rewrite <- H1.
  clear NIL_CASE H1.
  destruct a0; try discriminate. simpl in t0. subst t0. simpl in PLAIN.
  rename id into i0. rename t into t0. 
  revert H H0. generalize 0 at 1 2 4 5 6 7 8 9. revert i0 t0 v PLAIN NO_REPLI;
  induction m as [| a1 m]; intros.
  + simpl.
    if_tac; [| congruence].
    solve_mod_modulus.
    unfold alignof.
   apply derives_refl. 
  +
    destruct a1 as [i1 t1|]; try discriminate.
   simpl in PLAIN.
 match goal with
    | |- _ ⊢ struct_pred (Member_plain i0 t0 :: Member_plain i1 t1 :: m) ?P v ?p =>
           change (struct_pred (Member_plain i0 t0 :: Member_plain i1 t1 :: m) P v p) with
             (P (Member_plain i0 t0) (fst v) p ∗ struct_pred (Member_plain i1 t1 :: m) P (snd v) p);
           simpl (P (Member_plain i0 t0) (fst v) p)
    end.
    if_tac; [| congruence].
    solve_mod_modulus.
   destruct v as [v0 v1].
   rewrite members_no_replicate_ind in NO_REPLI; destruct NO_REPLI as [NOT_IN NO_REPLI].
    specialize (IHm i1 t1 v1 PLAIN NO_REPLI (align z (alignof t0) + sizeof t0)).
    simpl snd.
    fold (sizeof t0) in *. fold (alignof t0) in *.
    erewrite struct_pred_ext.
    fold (sizeof t0) in *. fold (alignof t0) in *.
    fold (sizeof t1) in *. fold (alignof t1) in *.
    rewrite <- IHm; [ |  simpl in H |- *; 
          fold (sizeof t0) in *; fold (alignof t0) in *;
          fold (sizeof t1) in *; fold (alignof t1) in *;
          pose_align_le; pose_sizeof_pos; lia
         | pose_align_le; pose_sizeof_pos; lia].
      replace (ofs + align (align z (alignof t0) + sizeof t0) (alignof t1)) with
        (ofs + align z (alignof t0) +
         (align (align z (alignof t0) + sizeof t0) (alignof t1) -
          align z (alignof t0))) by lia.
      rewrite <- mapsto_zeros_split by
        (simpl in H; 
          fold (sizeof t0) in *; fold (alignof t0) in *;
          fold (sizeof t1) in *; fold (alignof t1) in *;revert H; pose_align_le; pose_sizeof_pos; intros; lia).
     apply bi.equiv_entails_1_1; f_equiv; hnf; lia.
     auto.
     intros.
      solve_mod_modulus.
      rewrite !name_member_get.
      assert (i <> name_member (Member_plain i0 t0)).
      simpl. clear - H2 NOT_IN.  contradict NOT_IN. subst i0. simpl. auto.
      rewrite -> (neq_field_offset_rec_cons cenv_cs i (Member_plain i0 t0)) by auto.
      rewrite -> (neq_field_offset_next_rec_cons cenv_cs i (Member_plain i0 t0)) by auto.
      reflexivity.
Transparent mapsto_zeros.
Qed.

Lemma memory_block_union_pred: forall sh m sz {A} (v: compact_sum (map A m)) b ofs,
  (m = nil -> sz = 0) ->
  union_pred m (fun it _ => memory_block sh sz) v (Vptr b (Ptrofs.repr ofs)) =
  memory_block sh sz (Vptr b (Ptrofs.repr ofs)).
Proof.
  intros sh m sz A v b ofs NIL_CASE; intros.
  destruct m as [| a0 m].
  1: rewrite (NIL_CASE eq_refl) memory_block_zero; simpl; normalize.
  clear NIL_CASE.
  revert a0 v; induction m as [| a1 m]; intros.
  + simpl; auto.
  + destruct v.
    - simpl; auto.
    - apply IHm.
Qed.

Lemma mapsto_zeros_union_pred: forall sh m sz {A} (v: compact_sum (map A m)) b ofs,
  (m = nil -> sz = 0) ->
  mapsto_zeros sz sh (Vptr b (Ptrofs.repr ofs)) ⊢
  union_pred m (fun it _ => mapsto_zeros sz sh) v (Vptr b (Ptrofs.repr ofs)).
Proof.
  intros sh m sz A v b ofs NIL_CASE; intros.
  destruct m as [| a0 m].
  1: rewrite (NIL_CASE eq_refl) mapsto_zeros_zero; simpl; normalize.
  clear NIL_CASE.
  revert a0 v; induction m as [| a1 m]; intros.
  + simpl; auto.
  + destruct v.
    - simpl; auto.
    - apply IHm.
Qed.

End MEMORY_BLOCK_AGGREGATE.

End mpred.

Module aggregate_pred.

Open Scope Z.


Definition array_pred: forall `{!heapGS Σ}{A: Type}{d: Inhabitant A} (lo hi: Z) (P: Z -> A -> val -> mpred) (v: list A),
    val -> mpred := @array_pred.

Definition struct_pred: forall `{!heapGS Σ} (m: members) {A: member -> Type} (P: forall it, A it -> val -> mpred) (v: compact_prod (map A m)) (p: val), mpred := @struct_pred.

Definition union_pred: forall `{!heapGS Σ} (m: members) {A: member -> Type} (P: forall it, A it -> val -> mpred) (v: compact_sum (map A m)) (p: val), mpred := @union_pred.

Definition array_Prop: forall {A: Type} (d:A) (lo hi: Z) (P: Z -> A -> Prop) (v: list A), Prop := @array_Prop.

Definition struct_Prop: forall (m: members) {A: member -> Type} (P: forall it, A it -> Prop) (v: compact_prod (map A m)), Prop := @struct_Prop.

Definition union_Prop: forall (m: members) {A: member -> Type} (P: forall it, A it -> Prop) (v: compact_sum (map A m)), Prop := union_Prop.

Definition array_pred_len_0: forall `{!heapGS Σ}{A}{d: Inhabitant A} lo hi P p,
  hi = lo ->
  array_pred lo hi P nil p = emp
:= @array_pred_len_0.

Definition array_pred_len_1: forall `{!heapGS Σ} {A}{d: Inhabitant A} i (P : Z -> A -> _) v p,
  array_pred i (i + 1) P (v :: nil) p = P i v p
:= @array_pred_len_1.

Definition split_array_pred: forall `{!heapGS Σ} {A} {d: Inhabitant A} lo mid hi P v p,
  lo <= mid <= hi ->
  Zlength v = (hi-lo) ->
  array_pred lo hi P v p =
  (array_pred lo mid P (sublist 0 (mid-lo) v) p ∗
   array_pred mid hi P (sublist (mid-lo) (hi-lo) v) p)
:= @split_array_pred.

Definition array_pred_shift: forall `{!heapGS Σ} {A} {d: Inhabitant A} lo hi lo' hi' mv 
              P' P v p,
  lo - lo' = mv ->
  hi - hi' = mv ->
  (forall i i', lo <= i < hi -> i - i' = mv ->
           P' i' (Znth (i - lo) v) p = P i (Znth (i - lo) v) p) ->
  array_pred lo' hi' P' v p = array_pred lo hi P v p
:= @array_pred_shift.

Definition array_pred_ext_derives:
  forall `{!heapGS Σ} {A B} {dA: Inhabitant A} {dB: Inhabitant B} lo hi P0 P1 
            (v0: list A) (v1: list B) p,
  (Zlength v0 = hi - lo -> Zlength v1 = hi - lo) ->
  (forall i, lo <= i < hi ->
      P0 i (Znth (i-lo) v0) p ⊢ P1 i (Znth (i-lo) v1) p) ->
  array_pred lo hi P0 v0 p ⊢ array_pred lo hi P1 v1 p
:= @array_pred_ext_derives.

Definition array_pred_ext:
  forall `{!heapGS Σ} {A B} {dA: Inhabitant A} {dB: Inhabitant B} lo hi P0 P1 (v0: list A) (v1: list B)  p,
  Zlength v0 = Zlength v1 ->
  (forall i, lo <= i < hi ->
     P0 i (Znth (i - lo) v0) p ⊣⊢ P1 i (Znth (i - lo) v1) p) ->
  array_pred lo hi P0 v0 p ⊣⊢ array_pred lo hi P1 v1 p
:= @array_pred_ext.

Definition at_offset_array_pred: forall `{!heapGS Σ} {A} {d: Inhabitant A} lo hi P v ofs p,
  at_offset (array_pred lo hi P v) ofs p = array_pred lo hi (fun i v => at_offset (P i v) ofs) v p
:= @at_offset_array_pred.

Definition array_pred_sepcon: forall  `{!heapGS Σ} {A} {d: Inhabitant A} lo hi P Q (v: list A) p,
  (array_pred lo hi P v p ∗ array_pred lo hi Q v p) = array_pred lo hi (fun i v p => P i v p ∗ Q i v p) v p
:= @array_pred_sepcon.

Definition struct_pred_ramif: forall `{!heapGS Σ} m {A} (P: forall it, A it -> val -> mpred) (i: ident) v p d,
  in_members i m ->
  members_no_replicate m = true ->
  struct_pred m P v p ⊢
    P _ (proj_struct i m v d) p ∗
     (∀ v0, P _ v0 p -∗ struct_pred m P (upd_struct i m v v0) p)
:= @struct_pred_ramif.

Definition struct_pred_ext_derives:
  forall `{!heapGS Σ} m {A0 A1} (P0: forall it, A0 it -> val -> mpred) (P1: forall it, A1 it -> val -> mpred) v0 v1 p,
  members_no_replicate m = true ->
  (forall i d0 d1, in_members i m ->
     P0 _ (proj_struct i m v0 d0) p ⊢ P1 _ (proj_struct i m v1 d1) p) ->
  struct_pred m P0 v0 p ⊢ struct_pred m P1 v1 p
:= @struct_pred_ext_derives.

Definition struct_pred_ext:
  forall `{!heapGS Σ} m {A0 A1} (P0: forall it, A0 it -> val -> mpred) (P1: forall it, A1 it -> val -> mpred) v0 v1 p,
  members_no_replicate m = true ->
  (forall i d0 d1, in_members i m ->
     P0 _ (proj_struct i m v0 d0) p ⊣⊢ P1 _ (proj_struct i m v1 d1) p) ->
  struct_pred m P0 v0 p ⊣⊢ struct_pred m P1 v1 p
:= @struct_pred_ext.

Definition at_offset_struct_pred: forall `{!heapGS Σ} m {A} (P: forall it, A it -> val -> mpred) v p ofs,
  at_offset (struct_pred m P v) ofs p = struct_pred m (fun it v => at_offset (P it v) ofs) v p
:= @at_offset_struct_pred.

Definition andp_struct_pred: forall `{!heapGS Σ} m {A} (P: forall it, A it -> val -> mpred) v p Q {_ : Persistent Q} {_ : Absorbing Q},
  Q ∧ struct_pred m P v p ⊣⊢
  match m with
  | nil => Q ∧ emp
  | _ => struct_pred m (fun it v p => Q ∧ P it v p) v p
  end
:= @corable_andp_struct_pred.

Definition struct_pred_sepcon: forall `{!heapGS Σ} m {A} (P Q: forall it, A it -> val -> mpred) v p,
  (struct_pred m P v p ∗ struct_pred m Q v p) = struct_pred m (fun it v p => P it v p ∗ Q it v p) v p
:= @struct_pred_sepcon.

Definition union_pred_ramif: forall `{!heapGS Σ} m {A} (P: forall it, A it -> val -> mpred) (i: ident) v p d,
  (forall i' (v': A (get_member i' m)), in_members i' m -> P _ v' p ⊢ P _ d p) ->
  in_members i m ->
  members_no_replicate m = true ->
  union_pred m P v p ⊢
    P _ (proj_union i m v d) p ∗
     ∀ v0, P _ v0 p -∗ union_pred m P (upd_union i m v v0) p
:= @union_pred_ramif.

Definition union_pred_ext_derives:
  forall `{!heapGS Σ} m {A0 A1} (P0: forall it, A0 it -> val -> mpred) (P1: forall it, A1 it -> val -> mpred) v0 v1 p,
  members_no_replicate m = true ->
  (forall it, members_union_inj v0 it <-> members_union_inj v1 it) ->
  (forall i (Hin: in_members i m) d0 d1, members_union_inj v0 (get_member i m) -> members_union_inj v1 (get_member i m) ->
     P0 _ (proj_union i m v0 d0) p ⊢ P1 _ (proj_union i m v1 d1) p) ->
  union_pred m P0 v0 p ⊢ union_pred m P1 v1 p
:= @union_pred_ext_derives.

Definition union_pred_ext:
  forall `{!heapGS Σ} m {A0 A1} (P0: forall it, A0 it -> val -> mpred) (P1: forall it, A1 it -> val -> mpred) v0 v1 p,
  members_no_replicate m = true ->
  (forall it, members_union_inj v0 it <-> members_union_inj v1 it) ->
  (forall i (Hin: in_members i m) d0 d1, members_union_inj v0 (get_member i m) -> members_union_inj v1 (get_member i m) ->
     P0 _ (proj_union i m v0 d0) p ⊣⊢ P1 _ (proj_union i m v1 d1) p) ->
  union_pred m P0 v0 p ⊣⊢ union_pred m P1 v1 p
:= @union_pred_ext.

Definition at_offset_union_pred: forall `{!heapGS Σ} m {A} (P: forall it, A it -> val -> mpred) v p ofs,
  at_offset (union_pred m P v) ofs p = union_pred m (fun it v => at_offset (P it v) ofs) v p
:= @at_offset_union_pred.

Definition andp_union_pred: forall `{!heapGS Σ} m {A} (P: forall it, A it -> val -> mpred) v p Q,
  (Q ∧ union_pred m P v p) =
  match m with
  | nil => Q ∧ emp
  | _ => union_pred m (fun it v p => Q ∧ P it v p) v p
  end
:= @andp_union_pred.

Definition union_pred_sepcon: forall `{!heapGS Σ} m {A} (P Q: forall it, A it -> val -> mpred) v p,
  (union_pred m P v p ∗ union_pred m Q v p) = union_pred m (fun it v p => P it v p ∗ Q it v p) v p
:= @union_pred_sepcon.

Definition struct_Prop_compact_prod_gen: forall m (F: member -> Type) (P: forall it, F it -> Prop) (f: forall it, F it),
  members_no_replicate m = true ->
  (forall i, in_members i m -> P (get_member i m) (f (get_member i m))) ->
  struct_Prop m P (compact_prod_gen f m)
:= @struct_Prop_compact_prod_gen.

Definition struct_Prop_proj: forall m (F: member -> Type) (P: forall it, F it -> Prop) v i d,
  in_members i m ->
  struct_Prop m P v ->
  P (get_member i m) (proj_struct i m v d)
:= @struct_Prop_proj.

Definition union_Prop_compact_sum_gen: forall m (F: member -> Type) (P: forall it, F it -> Prop) (f: forall it, F it),
  members_no_replicate m = true ->
  (forall i, in_members i m -> P (get_member i m) (f (get_member i m))) ->
  union_Prop m P (compact_sum_gen (fun _ => true) f m)
:= @union_Prop_compact_sum_gen.

Definition union_Prop_proj: forall m (F: member -> Type) (P: forall it, F it -> Prop) v i d,
  members_union_inj v (get_member i m) ->
  union_Prop m P v ->
  P (get_member i m) (proj_union i m v d)
:= @union_Prop_proj.

Definition array_pred_local_facts: forall `{!heapGS Σ} {A} {d: Inhabitant A} lo hi P v p Q,
  (forall i x, lo <= i < hi -> P i x p ⊢ ⌜Q x⌝) ->
  array_pred lo hi P v p ⊢ ⌜Zlength v = hi - lo /\ Forall Q v⌝
:= @array_pred_local_facts.

Definition struct_pred_local_facts: forall `{!heapGS Σ} m {A} (P: forall it, A it -> val -> mpred)v p (R: forall it, A it -> Prop),
  members_no_replicate m = true ->
  (forall i v0, in_members i m -> P (get_member i m) v0 p ⊢ ⌜R _ v0⌝) ->
  struct_pred m P v p ⊢ ⌜struct_Prop m R v⌝
:= @struct_pred_local_facts.

Definition union_pred_local_facts: forall `{!heapGS Σ} m {A} (P: forall it, A it -> val -> mpred)v p (R: forall it, A it -> Prop),
  members_no_replicate m = true ->
  (forall i v0, in_members i m -> P (get_member i m) v0 p ⊢ ⌜R _ v0⌝) ->
  union_pred m P v p ⊢ ⌜union_Prop m R v⌝
:= @union_pred_local_facts.

End aggregate_pred.

Require Import VST.floyd.reptype_lemmas.

(******************************************

Auxiliary predicates

******************************************)

Section AUXILIARY_PRED.

Context `{!heapGS Σ} {cs: compspecs}.

Variable sh: share.

Definition struct_data_at_rec_aux (m m0: members) (sz: Z) 
       (P: hlist (tmap (fun it => reptype (field_type (name_member it) m0) -> (val -> mpred)) m))
       (v: compact_prod (map (fun it => reptype (field_type (name_member it) m0)) m)) : (val -> mpred).
Proof.
  destruct m as [| a0 m]; [exact (fun _ => emp) |].
  revert a0 v P; induction m as [| a0 m]; intros ? v P.
  + simpl in v, P.
    inversion P; subst.
    exact (withspacer sh
            (field_offset cenv_cs (name_member a0) m0 + sizeof (field_type (name_member a0) m0))
            (field_offset_next cenv_cs (name_member a0) m0 sz)
            (at_offset (X v) (field_offset cenv_cs (name_member a0) m0))).
  + simpl in v, P.
    inversion P; subst.
    exact (fun v0 => withspacer sh
            (field_offset cenv_cs (name_member a1) m0 + sizeof (field_type (name_member a1) m0))
            (field_offset_next cenv_cs (name_member a1) m0 sz)
            (at_offset (X (fst v)) (field_offset cenv_cs (name_member a1) m0)) v0 ∗ IHm a0 (snd v) X0 v0).
Defined.

Definition union_data_at_rec_aux (m m0: members) (sz: Z)
      (P: hlist (tmap (fun it => reptype (field_type (name_member it) m0) -> (val -> mpred)) m))
      (v: compact_sum (map (fun it => reptype (field_type (name_member it) m0)) m)) : (val -> mpred).
Proof.
  destruct m as [| a0 m]; [exact (fun _ => emp) |].
  revert a0 v P; induction m as [| a0 m]; intros ? v P.
  + simpl in v, P.
    inversion P; subst.
    exact (withspacer sh (sizeof (field_type (name_member a0) m0)) sz (X v)).
  + simpl in v, P.
    inversion P; subst.
    destruct v as [v | v].
    - exact (withspacer sh (sizeof (field_type (name_member a1) m0)) sz (X v)).
    - exact (IHm a0 v X0).
Defined.

Lemma struct_data_at_rec_aux_spec: forall m m0 sz v P,
  struct_data_at_rec_aux m m0 sz
   (hmap
     (fun it => reptype (field_type (name_member it) m0) -> val -> mpred)
     P m) v =
  struct_pred m
   (fun it v =>
      withspacer sh
       (field_offset cenv_cs (name_member it) m0 + sizeof (field_type (name_member it) m0))
       (field_offset_next cenv_cs (name_member it) m0 sz)
       (at_offset (P it v) (field_offset cenv_cs (name_member it) m0))) v.
Proof.
  intros.
  destruct m as [| a0 m]; [reflexivity |].
  revert a0 v; induction m as [| a0 m]; intros.
  + simpl; reflexivity.
  + change
     (struct_data_at_rec_aux (a1 :: a0 :: m) m0 sz
     (hmap (fun it : member => reptype (field_type (name_member it) m0) -> val -> mpred)
        P (a1 :: a0 :: m)) v) with
     (fun v0 => withspacer sh
       (field_offset cenv_cs (name_member a1) m0 + sizeof (field_type (name_member a1) m0))
         (field_offset_next cenv_cs (name_member a1) m0 sz)
           (at_offset (P a1 (fst v)) (field_offset cenv_cs (name_member a1) m0)) v0 ∗
      struct_data_at_rec_aux (a0 :: m) m0 sz
     (hmap (fun it : member => reptype (field_type (name_member it) m0) -> val -> mpred)
        P (a0 :: m)) (snd v) v0).
    rewrite IHm //.
Qed.

Lemma union_data_at_rec_aux_spec: forall m m0 sz v P,
  union_data_at_rec_aux m m0 sz
   (hmap
     (fun it => reptype (field_type (name_member it) m0) -> val -> mpred)
     P m) v =
  union_pred m
   (fun it v =>
      withspacer sh
       (sizeof (field_type (name_member it) m0))
       sz
       (P it v)) v.
Proof.
  intros.
  destruct m as [| a0 m]; [reflexivity |].
  revert a0 v; induction m as [| a0 m]; intros.
  + reflexivity.
  + destruct v as [v | v].
    - reflexivity.
    - match goal with
      | _ => apply IHm
      | _ => simpl; f_equal; apply IHm
      end.
Qed.

Definition struct_value_fits_aux (m m0: members)
      (P: hlist (tmap (fun it => reptype (field_type (name_member it) m0) -> Prop) m))
      (v: compact_prod (map (fun it => reptype (field_type (name_member it) m0)) m)) : Prop.
Proof.
  destruct m as [| a0 m]; [exact True%type |].
  revert a0 v P; induction m as [| a0 m]; intros ? v P.
  + simpl in v, P.
    inversion P; subst.
    apply (X v).
  + simpl in v, P.
    inversion P; subst.
    apply (X (fst v) /\ IHm a0 (snd v) X0).
Defined.

Definition union_value_fits_aux (m m0: members)
      (P: hlist (tmap (fun it => reptype (field_type (name_member it) m0) -> Prop) m))
      (v: compact_sum (map (fun it => reptype (field_type (name_member it) m0)) m)) : Prop.
Proof.
  destruct m as [| a0 m]; [exact True%type |].
  revert a0 v P; induction m as [| a0 m]; intros ? v P.
  + simpl in v, P.
    inversion P; subst.
    exact (X v).
  + simpl in v, P.
    inversion P; subst.
    destruct v as [v | v].
    - exact (X v).
    - exact (IHm a0 v X0).
Defined.

Lemma struct_value_fits_aux_spec: forall m m0 v P,
  struct_value_fits_aux m m0
   (hmap
     (fun it => reptype (field_type (name_member it) m0) -> Prop)
     P m) v =
  struct_Prop m P v.
Proof.
  intros.
  destruct m as [| a0 m]; [reflexivity |].
  revert a0 v; induction m as [| a0 m]; intros.
  + simpl; reflexivity.
  + change
     (struct_value_fits_aux (a1 :: a0 :: m) m0
     (hmap (fun it : member => reptype (field_type (name_member it) m0) -> Prop)
        P (a1 :: a0 :: m)) v) with
     (P a1 (fst v) /\  struct_value_fits_aux (a0 :: m) m0
     (hmap (fun it : member => reptype (field_type (name_member it) m0) -> Prop)
        P (a0 :: m)) (snd v)).
    rewrite IHm //.
Qed.

Lemma union_value_fits_aux_spec: forall m m0 v P,
  union_value_fits_aux m m0
   (hmap
     (fun it => reptype (field_type (name_member it) m0) -> Prop)
     P m) v =
  union_Prop m P v.
Proof.
  intros.
  destruct m as [| a0 m]; [reflexivity |].
  revert a0 v; induction m as [| a0 m]; intros.
  + reflexivity.
  + destruct v as [v | v].
    - reflexivity.
    - match goal with
      | _ => apply IHm
      | _ => simpl; f_equal; apply IHm
      end.
Qed.

End AUXILIARY_PRED.

Module auxiliary_pred.

Import aggregate_pred.

Definition struct_data_at_rec_aux:
   forall `{!heapGS Σ} {cs: compspecs} (sh: share) (m m0: members) (sz: Z) 
     (P: hlist (tmap (fun it => reptype (field_type (name_member it) m0) -> (val -> mpred)) m)) 
     (v: compact_prod (map (fun it => reptype (field_type (name_member it) m0)) m)), (val -> mpred)
:= @struct_data_at_rec_aux.

Definition union_data_at_rec_aux:
  forall `{!heapGS Σ} {cs: compspecs} (sh: share) (m m0: members) (sz: Z) 
    (P: hlist (tmap (fun it => reptype (field_type (name_member it) m0) -> (val -> mpred)) m)) 
    (v: compact_sum (map (fun it => reptype (field_type (name_member it) m0)) m)), (val -> mpred)
:= @union_data_at_rec_aux.

Definition struct_data_at_rec_aux_spec: forall `{!heapGS Σ} {cs: compspecs} (sh: share) m m0 sz v P,
  struct_data_at_rec_aux sh m m0 sz
   (hmap
     (fun it => reptype (field_type (name_member it) m0) -> val -> mpred)
     P m) v =
  struct_pred m
   (fun it v =>
      withspacer sh
       (field_offset cenv_cs (name_member it) m0 + sizeof (field_type (name_member it) m0))
       (field_offset_next cenv_cs (name_member it) m0 sz)
       (at_offset (P it v) (field_offset cenv_cs (name_member it) m0))) v
:= @struct_data_at_rec_aux_spec.

Definition union_data_at_rec_aux_spec: forall `{!heapGS Σ} {cs: compspecs} sh m m0 sz v P,
  union_data_at_rec_aux sh m m0 sz
   (hmap
     (fun it => reptype (field_type (name_member it) m0) -> val -> mpred)
     P m) v =
  union_pred m
   (fun it v =>
      withspacer sh
       (sizeof (field_type (name_member it) m0))
       sz
       (P it v)) v
:= @union_data_at_rec_aux_spec.

Definition struct_value_fits_aux:
  forall {cs: compspecs} (m m0: members)
      (P: hlist (tmap (fun it => reptype (field_type (name_member it) m0) -> Prop) m))
      (v: compact_prod (map (fun it => reptype (field_type (name_member it) m0)) m)), Prop
:= @struct_value_fits_aux.

Definition union_value_fits_aux:
  forall {cs: compspecs} (m m0: members)
      (P: hlist (tmap (fun it => reptype (field_type (name_member it) m0) -> Prop) m))
      (v: compact_sum (map (fun it => reptype (field_type (name_member it) m0)) m)), Prop
:= @union_value_fits_aux.

Definition struct_value_fits_aux_spec: forall {cs: compspecs} m m0 v P,
  struct_value_fits_aux m m0
   (hmap
     (fun it => reptype (field_type (name_member it) m0) -> Prop)
     P m) v =
  struct_Prop m P v
:= @struct_value_fits_aux_spec.

Definition union_value_fits_aux_spec: forall {cs: compspecs} m m0 v P,
  union_value_fits_aux m m0
   (hmap
     (fun it => reptype (field_type (name_member it) m0) -> Prop)
     P m) v =
  union_Prop m P v
:= @union_value_fits_aux_spec.

Definition memory_block_array_pred:
  forall `{!heapGS Σ} {cs: compspecs} {A : Type} {d : Inhabitant A} (a: A) sh t z b ofs,
  0 <= z ->
  0 <= ofs /\ ofs + sizeof t * z < Ptrofs.modulus ->
  array_pred 0 z
     (fun i _ p =>
      memory_block sh (sizeof t)
        (offset_val (sizeof t * i) p)) (Zrepeat a z)
     (Vptr b (Ptrofs.repr ofs)) ⊣⊢
  memory_block sh (sizeof t * z) (Vptr b (Ptrofs.repr ofs))
:= @memory_block_array_pred'.

Definition mapsto_zeros_array_pred:
  forall `{!heapGS Σ} {cs: compspecs} {A : Type} {d : Inhabitant A} (a: A) sh t z b ofs,
  0 <= z ->
  0 <= ofs /\ ofs + sizeof t * z < Ptrofs.modulus ->
  mapsto_zeros (sizeof t * z) sh (Vptr b (Ptrofs.repr ofs)) ⊢
  array_pred 0 z
     (fun i _ p =>
      mapsto_zeros (sizeof t) sh
        (offset_val (sizeof t * i) p)) (Zrepeat a z)
     (Vptr b (Ptrofs.repr ofs))
:= @mapsto_zeros_array_pred'.

Definition memory_block_struct_pred:
  forall `{!heapGS Σ} {cs: compspecs} sh m sz {A} (v: compact_prod (map A m)) b ofs,
  (m = nil -> sz = 0) ->
  plain_members m = true ->
  members_no_replicate m = true ->
  sizeof_struct cenv_cs 0 m <= sz < Ptrofs.modulus ->
  0 <= ofs /\ ofs + sz < Ptrofs.modulus ->
  struct_pred m
   (fun it _ p =>
     (memory_block sh (field_offset_next cenv_cs (name_member it) m sz - field_offset cenv_cs (name_member it) m))
     (offset_val (field_offset cenv_cs (name_member it) m) p)) v (Vptr b (Ptrofs.repr ofs)) ⊣⊢
  memory_block sh sz (Vptr b (Ptrofs.repr ofs))
:= @memory_block_struct_pred.

Definition mapsto_zeros_struct_pred:
  forall `{!heapGS Σ} {cs: compspecs} sh m sz {A} (v: compact_prod (map A m)) b ofs,
  (m = nil -> sz = 0) ->
  plain_members m = true ->
  members_no_replicate m = true ->
  sizeof_struct cenv_cs 0 m <= sz < Ptrofs.modulus ->
  0 <= ofs /\ ofs + sz < Ptrofs.modulus ->
  mapsto_zeros sz sh (Vptr b (Ptrofs.repr ofs)) ⊢
  struct_pred m
   (fun it _ p =>
     (mapsto_zeros (field_offset_next cenv_cs (name_member it) m sz - field_offset cenv_cs (name_member it) m)) sh
     (offset_val (field_offset cenv_cs (name_member it) m) p)) v (Vptr b (Ptrofs.repr ofs))
:= @mapsto_zeros_struct_pred.

Definition memory_block_union_pred:
  forall `{!heapGS Σ} sh m sz {A} (v: compact_sum (map A m)) b ofs,
  (m = nil -> sz = 0) ->
  union_pred m (fun it _ => memory_block sh sz) v (Vptr b (Ptrofs.repr ofs)) =
  memory_block sh sz (Vptr b (Ptrofs.repr ofs))
:= @memory_block_union_pred.

Definition mapsto_zeros_union_pred:
  forall `{!heapGS Σ} sh m sz {A} (v: compact_sum (map A m)) b ofs,
  (m = nil -> sz = 0) ->
  mapsto_zeros sz sh (Vptr b (Ptrofs.repr ofs)) ⊢
  union_pred m (fun it _ => mapsto_zeros sz sh) v (Vptr b (Ptrofs.repr ofs))
:= @mapsto_zeros_union_pred.

End auxiliary_pred.
