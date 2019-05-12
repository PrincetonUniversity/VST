Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.type_induction.
(*Require Import VST.floyd.fieldlist.*)
Require Import VST.floyd.compact_prod_sum.
(*Require Import VST.floyd.aggregate_type.*)
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.nested_pred_lemmas.
Require Import VST.floyd.jmeq_lemmas.
Require Import VST.floyd.sublist.

Require Export VST.floyd.fieldlist.
Require Export VST.floyd.aggregate_type.

Open Scope Z.
Open Scope logic.

(******************************************

Definition and lemmas about rangespec

******************************************)

Fixpoint rangespec (lo: Z) (n: nat) (P: Z -> val -> mpred): val -> mpred :=
  match n with
  | O => fun _ => emp
  | S n' => P lo * rangespec (Z.succ lo) n' P
 end.

Fixpoint fold_range' {A: Type} (f: Z -> A -> A) (zero: A) (lo: Z) (n: nat) : A :=
 match n with
  | O => zero
  | S n' => f lo (fold_range' f  zero (Z.succ lo) n')
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
      apply derives_refl.
  + erewrite H; eauto.
      apply derives_refl.
    omega.
Qed.

Lemma rangespec_ext: forall lo len P P' p,
  (forall i, lo <= i < lo + Z_of_nat len -> P i p = P' i p) ->
  rangespec lo len P p = rangespec lo len P' p.
Proof.
  intros; apply pred_ext; apply rangespec_ext_derives;
  intros; rewrite H; auto.
Qed.

Lemma rangespec_sepcon: forall lo len P Q p,
  rangespec lo len P p * rangespec lo len Q p = rangespec lo len (P * Q) p.
Proof.
  intros.
  revert lo; induction len; intros.
  + simpl.
    rewrite sepcon_emp; auto.
  + simpl.
    rewrite !sepcon_assoc.
    f_equal.
    rewrite <- sepcon_assoc, (sepcon_comm _ (Q lo p)), sepcon_assoc.
    f_equal.
    rewrite IHlen.
    reflexivity.
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

Definition array_pred {A: Type}{d: Inhabitant A}  (lo hi: Z) (P: Z -> A -> val -> mpred) (v: list A) (p: val) : mpred :=
  !! (Zlength v = hi - lo) &&
  rangespec lo (Z.to_nat (hi-lo)) (fun i => P i (Znth (i-lo) v)) p.

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

Lemma array_pred_len_0: forall {A}{d: Inhabitant A} lo hi P p,
  hi = lo ->
  array_pred lo hi P nil p = emp.
Proof.
  intros.
  unfold array_pred.
  replace (Z.to_nat (hi - lo)) with 0%nat by (symmetry; apply Z_to_nat_neg; omega).
  simpl.
  rewrite prop_true_andp by (unfold Zlength; simpl; omega).
  reflexivity.
Qed.

Lemma array_pred_len_1: forall {A}{d: Inhabitant A} i P v p,
  array_pred i (i + 1) P (v :: nil) p = P i v p.
Proof.
  intros.
  unfold array_pred.
  replace (i + 1 - i) with 1 by omega.
  simpl. rewrite sepcon_emp.
  rewrite prop_true_andp by (unfold Zlength; simpl; omega).
  unfold Znth. rewrite Z.sub_diag. rewrite if_false by omega. change (Z.to_nat 0) with 0%nat. auto.
Qed.

Lemma split_array_pred: forall {A}{d: Inhabitant A} lo mid hi P v p,
  lo <= mid <= hi ->
  Zlength v = hi - lo ->
  array_pred lo hi P v p =
  array_pred lo mid P (sublist 0 (mid-lo) v) p *
  array_pred mid hi P (sublist (mid-lo) (hi-lo) v) p.
Proof.
  intros.
  unfold array_pred.
  normalize.
  rewrite prop_true_andp by (rewrite !Zlength_sublist by omega; omega).
  clear H0.
  remember (Z.to_nat (mid-lo)) as n.
  replace (Z.to_nat (hi-lo)) with (n + Z.to_nat (hi-mid))%nat in *
    by (subst n; rewrite <- Z2Nat.inj_add by omega; f_equal; omega).
  assert (lo = mid - Z.of_nat n)
    by (rewrite Heqn; rewrite Z2Nat.id by omega; omega).
  clear Heqn.
  revert lo v H H0; induction n; intros.
  + subst lo.
    change (Z.of_nat 0) with 0 in *.
    simpl rangespec at 2. rewrite emp_sepcon.
    rewrite Z.sub_0_r, Z.sub_diag, plus_0_l.
    apply rangespec_ext; intros.
    rewrite Z2Nat.id in H0 by omega.
    f_equal.
    rewrite Znth_sublist, Z.add_0_r by omega.
    reflexivity.
  + simpl plus at 1.
    unfold rangespec; fold rangespec.
    repeat match goal with |- context [(?A * ?B) p] => change ((A*B)p) with (A p * B p) end.
    rewrite !sepcon_assoc.
    f_equal.
    - f_equal.
      rewrite Z.sub_diag.
      subst lo.
      rewrite Znth_sublist by (try rewrite Nat2Z.inj_succ; omega).
      reflexivity.
    - replace (rangespec (Z.succ lo) (n + Z.to_nat (hi - mid))
              (fun i : Z => P i (Znth (i - lo) v)) p)
      with (rangespec (Z.succ lo) (n + Z.to_nat (hi - mid))
              (fun i : Z => P i (Znth (i - Z.succ lo) (skipn 1 v))) p).
      2:{
        apply rangespec_ext; intros.
        f_equal.
        rewrite <- Znth_succ by omega; auto.
      }
      rewrite Nat2Z.inj_succ in H0.
      rewrite IHn by omega.
      f_equal.
      * apply rangespec_ext; intros.
        f_equal.
        rewrite Znth_sublist, Z.add_0_r by omega.
        rewrite <- Znth_succ by omega; auto.
        rewrite Znth_sublist, Z.add_0_r by omega.
        reflexivity.
      * apply rangespec_ext; intros.
        f_equal.
        rewrite Z2Nat.id in H1 by omega.
        rewrite Znth_sublist by omega.
        rewrite Znth_sublist by omega.
        replace (i - mid + (mid - Z.succ lo)) with (i - Z.succ lo) by omega.
        rewrite <- Znth_succ by omega; auto.
         f_equal; omega.
Qed.

Lemma array_pred_shift: forall {A}{d: Inhabitant A} (lo hi lo' hi' mv : Z) P' P v p,
  lo - lo' = mv ->
  hi - hi' = mv ->
 (forall i i', lo <= i < hi -> i - i' = mv -> P' i' (Znth (i-lo) v) p = P i (Znth (i-lo) v) p) ->
  array_pred lo' hi' P' v p = array_pred lo hi P v p.
Proof.
  intros.
  unfold array_pred.
  apply andp_prop_ext; [omega | intros].
  replace (hi' - lo') with (hi - lo) by omega.
  destruct (zlt hi lo). rewrite Z2Nat_neg by omega. reflexivity.
  apply pred_ext; apply rangespec_shift_derives; intros.
  rewrite H4; rewrite Z2Nat.id in H3 by omega.
  rewrite H1; auto; omega.
  rewrite <- H4; rewrite Z2Nat.id in H3 by omega.
  rewrite H1; auto; omega.
Qed.

Lemma array_pred_ext_derives: forall {A B} (dA: Inhabitant A) (dB: Inhabitant B)
         lo hi P0 P1 (v0: list A) v1 p,
  (Zlength v0 = hi - lo -> Zlength v1 = hi - lo) ->
  (forall i, lo <= i < hi ->
    P0 i (Znth (i-lo) v0) p |-- P1 i (Znth (i-lo) v1) p) ->
  array_pred  lo hi P0 v0 p |-- array_pred lo hi P1 v1 p.
Proof.
  intros.
  unfold array_pred.
  normalize.
  rewrite prop_true_andp by omega.
  apply rangespec_ext_derives.
  intros.
  destruct (zlt hi lo).
  + rewrite Z2Nat_neg  in H2 by omega.
    change (Z.of_nat 0) with 0 in H2. omega.
  + rewrite Z2Nat.id in H2 by omega.
    apply H0. omega.
Qed.

Lemma array_pred_ext: forall {A B} (dA: Inhabitant A) (dB: Inhabitant B) lo hi P0 P1 
        (v0: list A) (v1: list B) p,
  Zlength v0 = Zlength v1 ->
  (forall i, lo <= i < hi ->
    P0 i (Znth (i-lo) v0) p = P1 i (Znth (i-lo) v1) p) ->
  array_pred lo hi P0 v0 p = array_pred lo hi P1 v1 p.
Proof.
  intros; apply pred_ext; apply array_pred_ext_derives; intros; try omega;
  rewrite H0; auto.
Qed.

Lemma at_offset_array_pred: forall  {A} {d: Inhabitant A} lo hi P v ofs p,
  at_offset (array_pred lo hi P v) ofs p = array_pred lo hi (fun i v => at_offset (P i v) ofs) v p.
Proof.
  intros.
  rewrite at_offset_eq.
  unfold array_pred.
  f_equal.
  apply rangespec_shift.
  intros.
  assert (i = i') by omega; subst i'; clear H0.
  rewrite at_offset_eq.
  auto.
Qed.

Lemma array_pred_sepcon: forall  {A} {d: Inhabitant A} lo hi P Q v p,
  array_pred lo hi P v p * array_pred lo hi Q v p = array_pred lo hi (P * Q) v p.
Proof.
  intros.
  unfold array_pred.
  normalize.
  apply andp_prop_ext; [omega | intros].
  rewrite rangespec_sepcon.
  auto.
Qed.

Opaque member_dec.

Lemma struct_pred_ext_derives: forall m {A0 A1} (P0: forall it, A0 it -> val -> mpred) (P1: forall it, A1 it -> val -> mpred) v0 v1 p,
  members_no_replicate m = true ->
  (forall i d0 d1, in_members i m ->
     P0 _ (proj_struct i m v0 d0) p |-- P1 _ (proj_struct i m v1 d1) p) ->
  struct_pred m P0 v0 p |-- struct_pred m P1 v1 p.
Proof.
  unfold proj_struct, field_type.
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
                else Ctypes.field_type i m) with (Ctypes.field_type i ((i1, t1) :: m)) in H0.
        destruct (member_dec
             (i,
             match Ctypes.field_type i ((i1, t1) :: m) with
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
  intros; erewrite H0 by eauto; auto;      apply derives_refl.
Qed.

Lemma struct_pred_not_member: forall m {A} (P: forall it, A it -> val -> mpred) (i: ident) v p,
  let P' it := if ident_eq i (fst it) then fun _ _ => emp else P it in
  ~ in_members i m ->
  struct_pred m P v p = struct_pred m P' v p.
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [auto |].
  unfold proj_struct, field_type in *.
  revert i0 t0 H v; induction m as [| (i1, t1) m]; intros i0 t0 H.
  + intros; subst P'; simpl.
    rewrite if_false; auto.
    intro; apply H; subst; left; auto.
  + set (M := (i1, t1) :: m).
    simpl compact_prod; simpl Ctypes.field_type.
    intros v.
    subst M.
    change (struct_pred ((i0, t0) :: (i1, t1) :: m) P v p)
      with (P _ (fst v) p * struct_pred ((i1, t1) :: m) P (snd v) p).
    change (struct_pred ((i0, t0) :: (i1, t1) :: m) P' v p)
      with (P' _ (fst v) p * struct_pred ((i1, t1) :: m) P' (snd v) p).
    destruct (ident_eq i i0).
    - subst P'; intros; subst.
      exfalso; apply H.
      left; auto.
    - intros.
      f_equal.
      * unfold P'.
        rewrite if_false by auto.
        auto.
      * apply IHm.
        intro; apply H; right; auto.
Qed.

Lemma struct_pred_proj: forall m {A} (P: forall it, A it -> val -> mpred) (i: ident) v p d,
  let P' it := if ident_eq i (fst it) then fun _ _ => emp else P it in
  members_no_replicate m = true ->
  in_members i m ->
  struct_pred m P v p = P _ (proj_struct i m v d) p * struct_pred m P' v p.
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [inv H0 |].
  unfold proj_struct, field_type in *.
  revert i0 t0 H v d H0; induction m as [| (i1, t1) m]; intros.
  + subst P'; simpl in *.
    destruct H0; [simpl in H0; subst i | tauto].
    destruct (ident_eq i0 i0); [| congruence].
    destruct (member_dec (i0, t0) (i0, t0)); [| congruence].
    unfold eq_rect_r; rewrite <- eq_rect_eq.
    rewrite sepcon_emp; auto.
  + pose proof H.
    apply members_no_replicate_ind in H1; destruct H1.
    set (M := (i1, t1) :: m).
    simpl compact_prod in v |- *; simpl Ctypes.field_type in d |- *.
    subst M.
    change (struct_pred ((i0, t0) :: (i1, t1) :: m) P v p)
      with (P _ (fst v) p * struct_pred ((i1, t1) :: m) P (snd v) p).
    change (struct_pred ((i0, t0) :: (i1, t1) :: m) P' v p)
      with (P' _ (fst v) p * struct_pred ((i1, t1) :: m) P' (snd v) p).
    destruct (ident_eq i i0).
    - subst i0.
      f_equal.
      * simpl.
        destruct (member_dec (i, t0) (i, t0)); [| congruence].
        unfold eq_rect_r; rewrite <- eq_rect_eq.
        auto.
      * erewrite struct_pred_not_member by eauto.
        unfold P' at 1.
        rewrite if_true by auto.
        rewrite emp_sepcon; auto.
    - intros.
      destruct H0; [simpl in H0; congruence |].
      rewrite <- sepcon_assoc, (sepcon_comm _ (P' _ _ _)), sepcon_assoc.
      f_equal.
      * unfold P'.
        rewrite if_false by (simpl; congruence).
        auto.
      * erewrite IHm by eauto.
        f_equal.
        simpl.
        match goal with
        | |- context [member_dec (i, ?t') (i0, t0)] =>
                destruct (member_dec (i, t') (i0, t0));
                  [inversion e; congruence |]
        end.
        auto.
Qed.

Lemma struct_pred_upd: forall m {A} (P: forall it, A it -> val -> mpred) (i: ident) v p v0,
  let P' it := if ident_eq i (fst it) then fun _ _ => emp else P it in
  members_no_replicate m = true ->
  in_members i m ->
  struct_pred m P (upd_struct i m v v0) p = P _ v0 p * struct_pred m P' v p.
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [inv H0 |].
  unfold proj_struct, field_type in *.
  revert i0 t0 H v v0 H0; induction m as [| (i1, t1) m]; intros.
  + subst P'; simpl in *.
    destruct H0; [simpl in H0; subst i | tauto].
    destruct (ident_eq i0 i0); [| congruence].
    destruct (member_dec (i0, t0) (i0, t0)); [| congruence].
    unfold eq_rect_r; rewrite <- eq_rect_eq.
    rewrite sepcon_emp; auto.
  + pose proof H.
    apply members_no_replicate_ind in H1; destruct H1.
    simpl compact_prod in v |- *; simpl Ctypes.field_type in v0 |- *.
    set (v' := (upd_struct i ((i0, t0) :: (i1, t1) :: m) v v0)).
    change (struct_pred ((i0, t0) :: (i1, t1) :: m) P v' p)
      with (P _ (fst v') p * struct_pred ((i1, t1) :: m) P (snd v') p).
    change (struct_pred ((i0, t0) :: (i1, t1) :: m) P' v p)
      with (P' _ (fst v) p * struct_pred ((i1, t1) :: m) P' (snd v) p).
    subst v'.
    simpl upd_struct.
    destruct (ident_eq i i0).
    - subst i0.
      destruct (member_dec (i, t0) (i, t0)); [| congruence].
      f_equal.
      * simpl.
        unfold eq_rect_r; rewrite <- eq_rect_eq.
        auto.
      * unfold eq_rect_r; rewrite <- eq_rect_eq.
        change (snd (v0, snd v)) with (snd v).
        erewrite struct_pred_not_member by eauto.
        unfold P' at 1.
        rewrite if_true by auto.
        rewrite emp_sepcon; auto.
    - destruct H0; [simpl in H0; congruence |].
      rewrite <- sepcon_assoc, (sepcon_comm _ (P' _ _ _)), sepcon_assoc.
      match goal with
      | |- context [member_dec (i, ?t') (i0, t0)] =>
              destruct (member_dec (i, t') (i0, t0));
                [inversion e; congruence |]
      end.
      f_equal.
      * unfold P'; simpl.
        rewrite if_false by (simpl; congruence).
        auto.
      * simpl snd.
        simpl in IHm |- *; erewrite IHm by auto.
        reflexivity.
Qed.

Lemma struct_pred_ramif: forall m {A} (P: forall it, A it -> val -> mpred) (i: ident) v p d,
  in_members i m ->
  members_no_replicate m = true ->
  struct_pred m P v p |--
    P _ (proj_struct i m v d) p *
     (ALL v0: _, P _ v0 p -* struct_pred m P (upd_struct i m v v0) p).
Proof.
  intros.
  set (P' it := if ident_eq i (fst it) then fun _ _ => emp else P it).
  apply RAMIF_Q.solve with (struct_pred m P' v p).
  + apply derives_refl'.
    apply struct_pred_proj; auto.
  + intro v0.
    apply derives_refl'.
    symmetry; rewrite sepcon_comm.
    apply struct_pred_upd; auto.
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

Lemma corable_andp_struct_pred: forall m {A} (P: forall it, A it -> val -> mpred) v p Q,
  corable Q ->
  Q && struct_pred m P v p =
  match m with
  | nil => Q && emp
  | _ => struct_pred m (fun it v p => Q && P it v p) v p
  end.
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [auto |].
  revert i0 t0 v; induction m as [| (i1, t1) m]; intros.
  + simpl.
    auto.
  + change (struct_pred ((i0, t0) :: (i1, t1) :: m) P v p)
      with (P (i0, t0) (fst v) p * struct_pred ((i1, t1) :: m) P (snd v) p).
    pattern Q at 1; rewrite <- (andp_dup Q).
    rewrite andp_assoc.
    rewrite <- corable_sepcon_andp1 by auto.
    rewrite IHm.
    rewrite <- corable_andp_sepcon1 by auto.
    reflexivity.
Qed.

Lemma struct_pred_sepcon: forall m {A} (P Q: forall it, A it -> val -> mpred) v p,
  struct_pred m P v p * struct_pred m Q v p = struct_pred m (fun it => P it * Q it) v p.
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [| revert i0 t0 v; induction m as [| (i1, t1) m]; intros].
  + simpl.
    rewrite emp_sepcon; auto.
  + simpl.
    auto.
  + change (struct_pred ((i0, t0) :: (i1, t1) :: m) P v p)
      with (P (i0, t0) (fst v) p * struct_pred ((i1, t1) :: m) P (snd v) p).
    change (struct_pred ((i0, t0) :: (i1, t1) :: m) Q v p)
      with (Q (i0, t0) (fst v) p * struct_pred ((i1, t1) :: m) Q (snd v) p).
    change (struct_pred ((i0, t0) :: (i1, t1) :: m) (fun it => P it * Q it) v p)
      with (P (i0, t0) (fst v) p * Q (i0, t0) (fst v) p * struct_pred ((i1, t1) :: m) (fun it => P it * Q it) (snd v) p).
    rewrite !sepcon_assoc; f_equal.
    rewrite <- sepcon_assoc, (sepcon_comm _ (Q _ _ _)), sepcon_assoc; f_equal.
    apply IHm.
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
  (forall i d0 d1, members_union_inj v0 (i, field_type i m) -> members_union_inj v1 (i, field_type i m) ->
     P0 _ (proj_union i m v0 d0) p |-- P1 _ (proj_union i m v1 d1) p) ->
  union_pred m P0 v0 p |-- union_pred m P1 v1 p.
Proof.
  unfold members_union_inj, proj_union, field_type.
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
    2:{
      clear - H.
      pose proof in_members_tail_no_replicate i0 _ _ _ H.
      intro HH; apply in_map with (f := fst) in HH.
      apply H0 in HH.
      tauto.
    }
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
        pose proof compact_sum_inj_in v0 (i, field_type i ((i1, t1) :: m)) member_dec.
        spec H0; [exact H2 |].
        subst.
        apply in_map with (f := fst) in H0.
        unfold fst at 1 in H0.
        tauto.
      * specialize (H1 d0 d1).
        change (if ident_eq i i1
                then Errors.OK t1
                else Ctypes.field_type i m) with (Ctypes.field_type i ((i1, t1) :: m)) in H1.
        destruct (member_dec
             (i,
             match Ctypes.field_type i ((i1, t1) :: m) with
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
  (forall i d0 d1, members_union_inj v0 (i, field_type i m) -> members_union_inj v1 (i, field_type i m) ->
     P0 _ (proj_union i m v0 d0) p = P1 _ (proj_union i m v1 d1) p) ->
  union_pred m P0 v0 p = union_pred m P1 v1 p.
Proof.
  intros.
  assert (forall it, members_union_inj v1 it <-> members_union_inj v0 it)
    by (intro it; specialize (H0 it); tauto).
  apply pred_ext; eapply union_pred_ext_derives; auto;
  intros; erewrite H1 by eauto; apply derives_refl.
Qed.

Lemma union_pred_derives_const: forall m {A} (P: forall it, A it -> val -> mpred) p v R,
  members_no_replicate m = true ->
  m <> nil ->
  (forall i (v: A (i, field_type i m)), in_members i m -> P _ v p |-- R) ->
  union_pred m P v p |-- R.
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [congruence |].
  clear H0.
  revert i0 t0 v H H1; induction m as [| (i1, t1) m]; intros.
  + simpl.
    specialize (H1 i0); simpl in H1.
    destruct (ident_eq i0 i0); [| congruence].
    apply H1; left; auto.
  + destruct v; simpl.
    - specialize (H1 i0); simpl in H1.
      destruct (ident_eq i0 i0); [| congruence].
      apply H1; left; auto.
    - pose proof H.
      rewrite members_no_replicate_ind in H; destruct H.
      apply (IHm i1 t1); auto.
      intros.
      specialize (H1 i).
      pose proof in_members_tail_no_replicate _ _ _ _ H0 H3.
      simpl in H1; destruct (ident_eq i i0); [congruence |].
      apply H1.
      right; auto.
Qed.

Lemma union_pred_proj: forall m {A} (P: forall it, A it -> val -> mpred) (i: ident) v p d,
  members_no_replicate m = true ->
  in_members i m ->
  (forall i' (v': A (i', field_type i' m)), in_members i' m -> P _ v' p |-- P _ d p) ->
  union_pred m P v p |-- P _ (proj_union i m v d) p.
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [inv H0 |].
  revert i0 t0 v d H H0 H1; induction m as [| (i1, t1) m]; intros.
  + destruct H0; [simpl in H0; subst i | tauto].
    simpl in *.
    destruct (ident_eq i0 i0); [| congruence].
    destruct (member_dec (i0, t0) (i0, t0)); [| congruence].
    unfold eq_rect_r; rewrite <- eq_rect_eq.
    auto.
  + pose proof H.
    rewrite members_no_replicate_ind in H; destruct H.
    simpl in *; destruct (ident_eq i i0), v.
    - subst i.
      destruct (member_dec (i0, t0) (i0, t0)); [| congruence].
      unfold eq_rect_r; rewrite <- eq_rect_eq.
      auto.
    - subst i.
      destruct (member_dec (i0, t0) (i0, t0)); [| congruence].
      unfold eq_rect_r; rewrite <- eq_rect_eq.
      apply (union_pred_derives_const ((i1, t1) :: m) P p y); [auto | congruence |].
      intros.
      specialize (H1 i).
      pose proof in_members_tail_no_replicate _ _ _ _ H2 H4.
      simpl in H1; destruct (ident_eq i i0); [congruence |].
      apply H1.
      right; auto.
    - match goal with
      | |- context [member_dec (i, ?t') (i0, t0)] =>
              destruct (member_dec (i, t') (i0, t0));
                [inversion e; congruence |]
      end.
      specialize (H1 i0).
      destruct (ident_eq i0 i0); [| congruence].
      apply H1.
      left; auto.
    - match goal with
      | |- context [member_dec (i, ?t') (i0, t0)] =>
              destruct (member_dec (i, t') (i0, t0));
                [inversion e; congruence |]
      end.
      apply (IHm i1 t1); auto.
      * destruct H0; [| auto].
        simpl in H0; congruence.
      * intros.
        specialize (H1 i').
        pose proof in_members_tail_no_replicate _ _ _ _ H2 H4.
        simpl in H1; destruct (ident_eq i' i0); [congruence |].
        apply H1.
        right; auto.
Qed.

Lemma union_pred_upd: forall m {A} (P: forall it, A it -> val -> mpred) (i: ident) v p v0,
  members_no_replicate m = true ->
  in_members i m ->
  union_pred m P (upd_union i m v v0) p = P _ v0 p.
Proof.
  intros.
  intros.
  unfold upd_union, upd_compact_sum.
  destruct (in_dec member_dec (i, field_type i m) m) as [?H | ?H];
    [| apply in_members_field_type in H0; tauto].
  clear v.
  destruct m as [| (i0, t0) m]; [inv H0 |].
  revert i0 t0 v0 H H0 H1; induction m as [| (i1, t1) m]; intros.
  + simpl in *.
    destruct H0; [simpl in H0; subst i | tauto].
    destruct (ident_eq i0 i0); [| congruence].
    destruct (member_dec (i0, t0) (i0, t0)); [| congruence].
    unfold eq_rect_r; rewrite <- eq_rect_eq.
    auto.
  + destruct H0; [simpl in H0; subst i |].
    - simpl in *.
      destruct (ident_eq i0 i0); [| congruence].
      destruct (member_dec (i0, t0) (i0, t0)); [| congruence].
      unfold eq_rect_r; rewrite <- eq_rect_eq.
      auto.
    - simpl in *.
      pose proof in_members_tail_no_replicate _ _ _ _ H H0.
      destruct (ident_eq i i0); [congruence |].
      match goal with
      | |- context [member_dec (i, ?t') (i0, t0)] =>
              destruct (member_dec (i, t') (i0, t0));
                [inversion e; congruence |]
      end.
      rewrite members_no_replicate_ind in H; destruct H.
      apply (IHm i1 t1); auto.
Qed.

Lemma union_pred_ramif: forall m {A} (P: forall it, A it -> val -> mpred) (i: ident) v p d,
  (forall i' (v': A (i', field_type i' m)), in_members i' m -> P _ v' p |-- P _ d p) ->
  in_members i m ->
  members_no_replicate m = true ->
  union_pred m P v p |--
    P _ (proj_union i m v d) p *
     (ALL v0: _, P _ v0 p -* union_pred m P (upd_union i m v v0) p).
Proof.
  intros.
  apply RAMIF_Q.solve with emp.
  + rewrite sepcon_emp.
    apply union_pred_proj; auto.
  + intro v0.
    rewrite emp_sepcon.
    apply derives_refl'.
    symmetry.
    apply union_pred_upd; auto.
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

Lemma andp_union_pred: forall m {A} (P: forall it, A it -> val -> mpred) v p Q,
  Q && union_pred m P v p =
  match m with
  | nil => Q && emp
  | _ => union_pred m (fun it v p => Q && P it v p) v p
  end.
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [auto |].
  revert i0 t0 v; induction m as [| (i1, t1) m]; intros.
  + simpl.
    auto.
  + destruct v.
    - simpl.
      auto.
    - simpl.
      apply IHm.
Qed.

Lemma union_pred_sepcon: forall m {A} (P Q: forall it, A it -> val -> mpred) v p,
  union_pred m P v p * union_pred m Q v p = union_pred m (fun it => P it * Q it) v p.
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [| revert i0 t0 v; induction m as [| (i1, t1) m]; intros].
  + simpl.
    rewrite sepcon_emp; auto.
  + simpl.
    auto.
  + destruct v.
    - simpl; auto.
    - apply IHm.
Qed.

Lemma struct_Prop_compact_prod_gen: forall m (F: ident * type -> Type) (P: forall it, F it -> Prop) (f: forall it, F it),
  members_no_replicate m = true ->
  (forall i, in_members i m -> P (i, field_type i m) (f (i, field_type i m))) ->
  struct_Prop m P (compact_prod_gen f m).
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [simpl; auto |].
  revert i0 t0 H H0; induction m as [| (i1, t1) m]; intros.
  + simpl.
    specialize (H0 i0).
    simpl in H0.
    rewrite if_true in H0 by auto.
    apply H0; left; auto.
  + change (struct_Prop ((i0, t0) :: (i1, t1) :: m) P
             (compact_prod_gen f ((i0, t0) :: (i1, t1) :: m)))
    with (P (i0, t0) (f (i0, t0)) /\
            struct_Prop ((i1, t1) :: m) P (compact_prod_gen f ((i1, t1) :: m))).
    split.
    - specialize (H0 i0).
      simpl in H0.
      rewrite if_true in H0 by auto.
      apply H0; left; auto.
    - rewrite members_no_replicate_ind in H; destruct H.
      apply (IHm i1 t1); auto.
      intros.
      specialize (H0 i).
      simpl in H0.
      destruct (ident_eq i i0); [subst; tauto |].
      apply H0; right; auto.
Qed.

Lemma struct_Prop_proj: forall m (F: ident * type -> Type) (P: forall it, F it -> Prop) v i d,
  in_members i m ->
  struct_Prop m P v ->
  P (i, field_type i m) (proj_struct i m v d).
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [inversion H |].
  revert i0 t0 v d H H0; induction m as [| (i1, t1) m]; intros.
  + inversion H; [simpl in H0; subst| tauto].
    simpl in *.
    destruct (ident_eq i0 i0); [| tauto].
    destruct (member_dec (i0, t0) (i0, t0)); [| tauto].
    unfold eq_rect_r; rewrite <- eq_rect_eq.
    auto.
  + destruct (ident_eq i i0).
    - subst.
      simpl in *.
      destruct (ident_eq i0 i0); [| tauto].
      destruct (member_dec (i0, t0) (i0, t0)); [| tauto].
      unfold eq_rect_r; rewrite <- eq_rect_eq.
      exact (proj1 H0).
    - assert (in_members i ((i1, t1) :: m)) by (inversion H; [subst; tauto | auto]).
      simpl in *.
      destruct (ident_eq i i0); [tauto |].
      destruct (member_dec
         (i,
         match
           (if ident_eq i i1 then Errors.OK t1 else Ctypes.field_type i m)
         with
         | Errors.OK t => t
         | Errors.Error _ => Tvoid
         end) (i0, t0)); [inversion e; subst; tauto |].
      apply IHm; auto.
      exact (proj2 H0).
Qed.

Lemma union_Prop_compact_sum_gen: forall m (F: ident * type -> Type) (P: forall it, F it -> Prop) (f: forall it, F it),
  members_no_replicate m = true ->
  (forall i, in_members i m -> P (i, field_type i m) (f (i, field_type i m))) ->
  union_Prop m P (compact_sum_gen (fun _ => true) f m).
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [simpl; auto |].
  destruct m as [| (i1, t1) m].
  + simpl.
    specialize (H0 i0).
    simpl in H0.
    rewrite if_true in H0 by auto.
    apply H0; left; auto.
  + simpl.
    specialize (H0 i0).
    simpl in H0.
    rewrite if_true in H0 by auto.
    apply H0; left; auto.
Qed.

Lemma union_Prop_proj: forall m (F: ident * type -> Type) (P: forall it, F it -> Prop) v i d,
  members_union_inj v (i, field_type i m) ->
  union_Prop m P v ->
  P (i, field_type i m) (proj_union i m v d).
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [inversion H |].
  revert i0 t0 v d H H0; induction m as [| (i1, t1) m]; intros.
  + simpl in H. if_tac in H; [| tauto].
    inversion H1; subst i.
    clear H1 H4.
    simpl in *.
    destruct (ident_eq i0 i0); [| tauto].
    destruct (member_dec (i0, t0) (i0, t0)); [| tauto].
    unfold eq_rect_r; rewrite <- eq_rect_eq.
    auto.
  + destruct (ident_eq i i0).
    - subst.
      simpl in *.
      destruct (ident_eq i0 i0); [| tauto].
      destruct (member_dec (i0, t0) (i0, t0)); [| tauto].
      unfold eq_rect_r; rewrite <- eq_rect_eq.
      destruct v; [| inversion H].
      auto.
    - assert (members_union_inj v (i, field_type i ((i1, t1) :: m))) by (simpl in H; destruct (ident_eq i i0); [tauto | auto]).
      simpl in *.
      destruct (ident_eq i i0); [tauto |].
      destruct (member_dec
         (i,
         match
           (if ident_eq i i1 then Errors.OK t1 else Ctypes.field_type i m)
         with
         | Errors.OK t => t
         | Errors.Error _ => Tvoid
         end) (i0, t0)); [inversion e; subst; tauto |].
      destruct v; [tauto |].
      apply IHm; auto.
Qed.

Lemma array_pred_local_facts: forall {A}{d: Inhabitant A} lo hi P v p Q,
  (forall i x, lo <= i < hi -> P i x p |-- !! Q x) ->
  array_pred lo hi P v p |-- !! (Zlength v = hi - lo /\ Forall Q v).
Proof.
  intros.
  unfold array_pred.
  normalize.
  rewrite prop_and; apply andp_right; [normalize |].
  pose proof ZtoNat_Zlength v.
  rewrite H0 in H1; symmetry in H1; clear H0.
  revert hi lo H H1; induction v; intros.
  + apply prop_right; constructor.
  + replace (hi - lo) with (Z.succ (hi - Z.succ lo)) in * by omega.
    assert (hi - Z.succ lo >= 0).
    {
      destruct (zlt (hi - Z.succ lo) 0); auto.
      assert (Z.succ (hi - Z.succ lo) <= 0) by omega.
      simpl length in H1.
      destruct (zeq (Z.succ (hi - Z.succ lo)) 0);
       [rewrite e in H1 | rewrite Z2Nat_neg in H1 by omega]; inv H1.
    }
    rewrite Z2Nat.inj_succ in H1 |- * by omega.
    inv H1.
    simpl rangespec.
    replace (rangespec (Z.succ lo) (length v)
              (fun i : Z => P i (Znth (i - lo) (a :: v))) p)
    with (rangespec (Z.succ lo) (length v)
            (fun i : Z => P i (Znth (i - Z.succ lo) v)) p).
    2:{
      apply rangespec_ext; intros.
      change v with (skipn 1 (a :: v)) at 1.
      rewrite <- Znth_succ by omega.
      auto.
    }
    rewrite H3.
    eapply derives_trans; [apply sepcon_derives; [apply H | apply IHv; auto] |].
    - omega.
    - intros; apply H; omega.
    - rewrite sepcon_prop_prop.
      apply prop_derives; intros.
      rewrite Z.sub_diag in H1; cbv in H1.
      constructor; tauto.
Qed.

Lemma struct_pred_local_facts: forall m {A} (P: forall it, A it -> val -> mpred)v p (R: forall it, A it -> Prop),
  members_no_replicate m = true ->
  (forall i v0, in_members i m -> P (i, field_type i m) v0 p |-- !! R _ v0) ->
  struct_pred m P v p |-- !! struct_Prop m R v.
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [simpl; apply prop_right; auto |].
  revert i0 t0 v H H0; induction m as [| (i1, t1) m]; intros.
  + simpl.
    specialize (H0 i0).
    simpl in H0.
    rewrite if_true in H0 by auto.
    apply H0; left; auto.
  + change (struct_Prop ((i0, t0) :: (i1, t1) :: m) R v)
      with (R (i0, t0) (fst v) /\ struct_Prop ((i1, t1) :: m) R (snd v)).
    change (struct_pred ((i0, t0) :: (i1, t1) :: m) P v p)
      with (P (i0, t0) (fst v) p * struct_pred ((i1, t1) :: m) P (snd v) p).
    rewrite members_no_replicate_ind in H.

    pose proof H0 i0.
    simpl in H1.
    if_tac in H1; [| congruence].
    specialize (H1 (fst v)).
    spec H1; [left; auto |].

    specialize (IHm i1 t1 (snd v)).
    spec IHm; [tauto |].
    eapply derives_trans; [apply sepcon_derives; [apply H1 | apply IHm] |].
    - intros.
      specialize (H0 i).
      simpl in H0.
      destruct (ident_eq i i0); [subst; tauto |].
      apply H0; right; auto.
    - rewrite sepcon_prop_prop; normalize.
Qed.

Lemma union_pred_local_facts: forall m {A} (P: forall it, A it -> val -> mpred)v p (R: forall it, A it -> Prop),
  members_no_replicate m = true ->
  (forall i v0, in_members i m -> P (i, field_type i m) v0 p |-- !! R _ v0) ->
  union_pred m P v p |-- !! union_Prop m R v.
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [simpl; apply prop_right; auto |].
  revert i0 t0 v H H0; induction m as [| (i1, t1) m]; intros.
  + simpl.
    specialize (H0 i0).
    simpl in H0.
    rewrite if_true in H0 by auto.
    apply H0; left; auto.
  + rewrite members_no_replicate_ind in H.
    destruct v.
    - simpl.
      pose proof H0 i0.
      simpl in H1.
      if_tac in H1; [| congruence].
      specialize (H1 a).
      apply H1; left; auto.
    - specialize (IHm i1 t1 c).
      spec IHm; [tauto |].
      apply IHm.
      intros.
      specialize (H0 i).
      simpl in H0.
      destruct (ident_eq i i0); [subst; tauto |].
      apply H0; right; auto.
Qed.

Section MEMORY_BLOCK_AGGREGATE.

Context {cs: compspecs}.

Lemma memory_block_array_pred: forall  {A}{d: Inhabitant A} sh t lo hi v b ofs,
  0 <= ofs + sizeof t * lo /\ ofs + sizeof t * hi < Ptrofs.modulus ->
  0 <= lo <= hi ->
  Zlength v = hi - lo ->
  array_pred lo hi
    (fun i _ p => memory_block sh (sizeof t) (offset_val (sizeof t * i) p)) v
    (Vptr b (Ptrofs.repr ofs)) =
   memory_block sh (sizeof t * (hi - lo)) (Vptr b (Ptrofs.repr (ofs + sizeof t * lo))).
Proof.
  intros.
  unfold array_pred.
  rewrite prop_true_andp by auto; clear H1.
  f_equal.
  remember (Z.to_nat (hi - lo)) as n eqn:HH.
  revert lo HH H H0 v; induction n; intros.
  + simpl.
    pose proof arith_aux00 _ _ (proj2 H0) HH.
    rewrite H1, Z.mul_0_r, memory_block_zero_Vptr.
    reflexivity.
  + simpl.
    pose proof arith_aux01 _ _ _ HH.
    solve_mod_modulus.
    pose_size_mult cenv_cs t (0 :: hi - Z.succ lo :: hi - lo :: nil).
    rewrite IHn; [| apply arith_aux02; auto | omega | omega | exact v].
    replace (ofs + sizeof  t * Z.succ lo) with (ofs + sizeof t * lo + sizeof t) by omega.
    rewrite <- memory_block_split by (auto; omega).
    f_equal.
    omega.
Qed.

Lemma memory_block_array_pred': forall {A}{d: Inhabitant A} (a: A) sh t z b ofs,
  0 <= z ->
  0 <= ofs /\ ofs + sizeof t * z < Ptrofs.modulus ->
  array_pred 0 z
     (fun i _ p =>
      memory_block sh (sizeof t) (offset_val (sizeof t * i) p))
             (list_repeat (Z.to_nat z) a)
     (Vptr b (Ptrofs.repr ofs))  =
  memory_block sh (sizeof t * z) (Vptr b (Ptrofs.repr ofs)).
Proof.
  intros.
  rewrite memory_block_array_pred.
  f_equal. f_equal. omega. f_equal. f_equal. rewrite Z.mul_0_r. omega.
  rewrite Z.mul_0_r. split; omega. omega.
  rewrite Z.sub_0_r. auto. rewrite Zlength_list_repeat', Z2Nat.id by omega.
  omega.
Qed.

Lemma memory_block_struct_pred: forall sh m sz {A} (v: compact_prod (map A m)) b ofs,
  (m = nil -> sz = 0) ->
  members_no_replicate m = true ->
  sizeof_struct cenv_cs 0 m <= sz < Ptrofs.modulus ->
  0 <= ofs /\ ofs + sz < Ptrofs.modulus ->
  struct_pred m
   (fun it _ p =>
     (memory_block sh (field_offset_next cenv_cs (fst it) m sz - field_offset cenv_cs (fst it) m))
     (offset_val (field_offset cenv_cs (fst it) m) p)) v (Vptr b (Ptrofs.repr ofs)) =
  memory_block sh sz (Vptr b (Ptrofs.repr ofs)).
Proof.
  unfold field_offset, Ctypes.field_offset, field_offset_next.
  intros sh m sz A v b ofs NIL_CASE NO_REPLI; intros.
  destruct m as [| (i0, t0) m].
  1: rewrite (NIL_CASE eq_refl), memory_block_zero; simpl; normalize.
  assert (align 0 (alignof t0) = 0) by apply align_0, alignof_pos.
  revert H0; pattern ofs at 1 4; replace ofs with (ofs + align 0 (alignof t0)) by omega; intros.
  revert H; pattern sz at 2 4; replace sz with (sz - align 0 (alignof t0)) by omega; intros.
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
      rewrite IHm with (z := align z (alignof t0) + sizeof t0);
        [| now auto
         | simpl in H |- *; pose_align_le; pose_sizeof_pos; omega
         | pose_align_le; pose_sizeof_pos; omega].
      replace (ofs + align (align z (alignof t0) + sizeof t0) (alignof t1)) with
        (ofs + align z (alignof t0) +
         (align (align z (alignof t0) + sizeof t0) (alignof t1) -
          align z (alignof t0))) by omega.
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
  union_pred m (fun it _ => memory_block sh sz) v (Vptr b (Ptrofs.repr ofs)) =
  memory_block sh sz (Vptr b (Ptrofs.repr ofs)).
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

Open Scope Z.
Open Scope logic.


Definition array_pred: forall {A: Type}{d: Inhabitant A} (lo hi: Z) (P: Z -> A -> val -> mpred) (v: list A),
    val -> mpred := @array_pred.

Definition struct_pred: forall (m: members) {A: ident * type -> Type} (P: forall it, A it -> val -> mpred) (v: compact_prod (map A m)) (p: val), mpred := @struct_pred.

Definition union_pred: forall (m: members) {A: ident * type -> Type} (P: forall it, A it -> val -> mpred) (v: compact_sum (map A m)) (p: val), mpred := @union_pred.

Definition array_Prop: forall {A: Type} (d:A) (lo hi: Z) (P: Z -> A -> Prop) (v: list A), Prop := @array_Prop.

Definition struct_Prop: forall (m: members) {A: ident * type -> Type} (P: forall it, A it -> Prop) (v: compact_prod (map A m)), Prop := @struct_Prop.

Definition union_Prop: forall (m: members) {A: ident * type -> Type} (P: forall it, A it -> Prop) (v: compact_sum (map A m)), Prop := union_Prop.

Definition array_pred_len_0: forall {A}{d: Inhabitant A} lo hi P p,
  hi = lo ->
  array_pred lo hi P nil p = emp
:= @array_pred_len_0.

Definition array_pred_len_1: forall {A}{d: Inhabitant A} i P v p,
  array_pred i (i + 1) P (v :: nil) p =  P i v p
:= @array_pred_len_1.

Definition split_array_pred: forall  {A}{d: Inhabitant A} lo mid hi P v p,
  lo <= mid <= hi ->
  Zlength v = (hi-lo) ->
  array_pred lo hi P v p =
  array_pred lo mid P (sublist 0 (mid-lo) v) p *
  array_pred mid hi P (sublist (mid-lo) (hi-lo) v) p
:= @split_array_pred.

Definition array_pred_shift: forall {A} {d: Inhabitant A} lo hi lo' hi' mv 
              P' P v p,
  lo - lo' = mv ->
  hi - hi' = mv ->
  (forall i i', lo <= i < hi -> i - i' = mv ->
           P' i' (Znth (i - lo) v) p = P i (Znth (i - lo) v) p) ->
  array_pred lo' hi' P' v p = array_pred lo hi P v p
:= @array_pred_shift.

Definition array_pred_ext_derives:
  forall {A B} {dA: Inhabitant A} {dB: Inhabitant B} lo hi P0 P1 
            (v0: list A) (v1: list B) p,
  (Zlength v0 = hi - lo -> Zlength v1 = hi - lo) ->
  (forall i, lo <= i < hi ->
      P0 i (Znth (i-lo) v0) p |-- P1 i (Znth (i-lo) v1) p) ->
  array_pred lo hi P0 v0 p |-- array_pred lo hi P1 v1 p
:= @array_pred_ext_derives.

Definition array_pred_ext:
  forall {A B} {dA: Inhabitant A} {dB: Inhabitant B} lo hi P0 P1 (v0: list A) (v1: list B)  p,
  Zlength v0 = Zlength v1 ->
  (forall i, lo <= i < hi ->
     P0 i (Znth (i - lo) v0) p = P1 i (Znth (i - lo) v1) p) ->
  array_pred lo hi P0 v0 p = array_pred lo hi P1 v1 p
:= @array_pred_ext.

Definition at_offset_array_pred: forall {A} {d: Inhabitant A} lo hi P v ofs p,
  at_offset (array_pred lo hi P v) ofs p = array_pred lo hi (fun i v => at_offset (P i v) ofs) v p
:= @at_offset_array_pred.

Definition array_pred_sepcon: forall  {A} {d: Inhabitant A} lo hi P Q v p,
  array_pred lo hi P v p * array_pred lo hi Q v p = array_pred lo hi (P * Q) v p
:= @array_pred_sepcon.

Definition struct_pred_ramif: forall m {A} (P: forall it, A it -> val -> mpred) (i: ident) v p d,
  in_members i m ->
  members_no_replicate m = true ->
  struct_pred m P v p |--
    P _ (proj_struct i m v d) p *
     allp ((fun v0: _ => P _ v0 p) -* (fun v0: _ => struct_pred m P (upd_struct i m v v0) p))
:= @struct_pred_ramif.

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

Definition andp_struct_pred: forall m {A} (P: forall it, A it -> val -> mpred) v p Q,
  corable Q ->
  Q && struct_pred m P v p =
  match m with
  | nil => Q && emp
  | _ => struct_pred m (fun it v p => Q && P it v p) v p
  end
:= @corable_andp_struct_pred.

Definition struct_pred_sepcon: forall m {A} (P Q: forall it, A it -> val -> mpred) v p,
  struct_pred m P v p * struct_pred m Q v p = struct_pred m (fun it => P it * Q it) v p
:= @struct_pred_sepcon.

Definition union_pred_ramif: forall m {A} (P: forall it, A it -> val -> mpred) (i: ident) v p d,
  (forall i' (v': A (i', field_type i' m)), in_members i' m -> P _ v' p |-- P _ d p) ->
  in_members i m ->
  members_no_replicate m = true ->
  union_pred m P v p |--
    P _ (proj_union i m v d) p *
     allp ((fun v0: _ => P _ v0 p) -* (fun v0 =>union_pred m P (upd_union i m v v0) p))
:= @union_pred_ramif.

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

Definition andp_union_pred: forall m {A} (P: forall it, A it -> val -> mpred) v p Q,
  Q && union_pred m P v p =
  match m with
  | nil => Q && emp
  | _ => union_pred m (fun it v p => Q && P it v p) v p
  end
:= @andp_union_pred.

Definition union_pred_sepcon: forall m {A} (P Q: forall it, A it -> val -> mpred) v p,
  union_pred m P v p * union_pred m Q v p = union_pred m (fun it => P it * Q it) v p
:= @union_pred_sepcon.

Definition struct_Prop_compact_prod_gen: forall m (F: ident * type -> Type) (P: forall it, F it -> Prop) (f: forall it, F it),
  members_no_replicate m = true ->
  (forall i, in_members i m -> P (i, field_type i m) (f (i, field_type i m))) ->
  struct_Prop m P (compact_prod_gen f m)
:= @struct_Prop_compact_prod_gen.

Definition struct_Prop_proj: forall m (F: ident * type -> Type) (P: forall it, F it -> Prop) v i d,
  in_members i m ->
  struct_Prop m P v ->
  P (i, field_type i m) (proj_struct i m v d)
:= @struct_Prop_proj.

Definition union_Prop_compact_sum_gen: forall m (F: ident * type -> Type) (P: forall it, F it -> Prop) (f: forall it, F it),
  members_no_replicate m = true ->
  (forall i, in_members i m -> P (i, field_type i m) (f (i, field_type i m))) ->
  union_Prop m P (compact_sum_gen (fun _ => true) f m)
:= @union_Prop_compact_sum_gen.

Definition union_Prop_proj: forall m (F: ident * type -> Type) (P: forall it, F it -> Prop) v i d,
  members_union_inj v (i, field_type i m) ->
  union_Prop m P v ->
  P (i, field_type i m) (proj_union i m v d)
:= @union_Prop_proj.

Definition array_pred_local_facts: forall {A} {d: Inhabitant A} lo hi P v p Q,
  (forall i x, lo <= i < hi -> P i x p |-- !! Q x) ->
  array_pred lo hi P v p |-- !! (Zlength v = hi - lo /\ Forall Q v)
:= @array_pred_local_facts.

Definition struct_pred_local_facts: forall m {A} (P: forall it, A it -> val -> mpred)v p (R: forall it, A it -> Prop),
  members_no_replicate m = true ->
  (forall i v0, in_members i m -> P (i, field_type i m) v0 p |-- !! R _ v0) ->
  struct_pred m P v p |-- !! struct_Prop m R v
:= @struct_pred_local_facts.

Definition union_pred_local_facts: forall m {A} (P: forall it, A it -> val -> mpred)v p (R: forall it, A it -> Prop),
  members_no_replicate m = true ->
  (forall i v0, in_members i m -> P (i, field_type i m) v0 p |-- !! R _ v0) ->
  union_pred m P v p |-- !! union_Prop m R v
:= @union_pred_local_facts.

End aggregate_pred.

Require Import VST.floyd.reptype_lemmas.

(******************************************

Auxiliary predicates

******************************************)

Section AUXILIARY_PRED.

Context {cs: compspecs}.

Variable sh: share.

Definition struct_data_at_rec_aux (m m0: members) (sz: Z) (P: ListType (map (fun it => reptype (field_type (fst it) m0) -> (val -> mpred)) m)) (v: compact_prod (map (fun it => reptype (field_type (fst it) m0)) m)) : (val -> mpred).
Proof.
  destruct m as [| (i0, t0) m]; [exact (fun _ => emp) |].
  revert i0 t0 v P; induction m as [| (i0, t0) m]; intros ? ? v P.
  + simpl in v, P.
    inversion P; subst.
    exact (withspacer sh
            (field_offset cenv_cs i0 m0 + sizeof (field_type i0 m0))
            (field_offset_next cenv_cs i0 m0 sz)
            (at_offset (a v) (field_offset cenv_cs i0 m0))).
  + simpl in v, P.
    destruct (ident_eq i1 i1); [| congruence].
    inversion P; subst.
    exact (withspacer sh
            (field_offset cenv_cs i1 m0 + sizeof (field_type i1 m0))
            (field_offset_next cenv_cs i1 m0 sz)
            (at_offset (a (fst v)) (field_offset cenv_cs i1 m0)) * IHm i0 t0 (snd v) b)%logic.
Defined.

Definition union_data_at_rec_aux (m m0: members) (sz: Z) (P: ListType (map (fun it => reptype (field_type (fst it) m0) -> (val -> mpred)) m)) (v: compact_sum (map (fun it => reptype (field_type (fst it) m0)) m)) : (val -> mpred).
Proof.
  destruct m as [| (i0, t0) m]; [exact (fun _ => emp) |].
  revert i0 t0 v P; induction m as [| (i0, t0) m]; intros ? ? v P.
  + simpl in v, P.
    inversion P; subst.
    exact (withspacer sh (sizeof (field_type i0 m0)) sz (a v)).
  + simpl in v, P.
    inversion P; subst.
    destruct v as [v | v].
    - exact (withspacer sh (sizeof (field_type i1 m0)) sz (a v)).
    - exact (IHm i0 t0 v b).
Defined.

Lemma struct_data_at_rec_aux_spec: forall m m0 sz v P,
  struct_data_at_rec_aux m m0 sz
   (ListTypeGen
     (fun it => reptype (field_type (fst it) m0) -> val -> mpred)
     P m) v =
  struct_pred m
   (fun it v =>
      withspacer sh
       (field_offset cenv_cs (fst it) m0 + sizeof (field_type (fst it) m0))
       (field_offset_next cenv_cs (fst it) m0 sz)
       (at_offset (P it v) (field_offset cenv_cs (fst it) m0))) v.
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [reflexivity |].
  revert i0 t0 v; induction m as [| (i0, t0) m]; intros.
  + simpl; reflexivity.
  + replace
     (struct_data_at_rec_aux ((i1, t1) :: (i0, t0) :: m) m0 sz
     (ListTypeGen (fun it : ident * type => reptype (field_type (fst it) m0) -> val -> mpred)
        P ((i1, t1) :: (i0, t0) :: m)) v) with
     (withspacer sh
       (field_offset cenv_cs i1 m0 + sizeof (field_type i1 m0))
         (field_offset_next cenv_cs i1 m0 sz)
           (at_offset (P (i1, t1) (fst v)) (field_offset cenv_cs i1 m0)) *
      struct_data_at_rec_aux ((i0, t0) :: m) m0 sz
     (ListTypeGen (fun it : ident * type => reptype (field_type (fst it) m0) -> val -> mpred)
        P ((i0, t0) :: m)) (snd v))%logic.
    - rewrite IHm.
      reflexivity.
    - simpl.
      destruct (ident_eq i1 i1); [| congruence].
      reflexivity.
Qed.

Lemma union_data_at_rec_aux_spec: forall m m0 sz v P,
  union_data_at_rec_aux m m0 sz
   (ListTypeGen
     (fun it => reptype (field_type (fst it) m0) -> val -> mpred)
     P m) v =
  union_pred m
   (fun it v =>
      withspacer sh
       (sizeof (field_type (fst it) m0))
       sz
       (P it v)) v.
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [reflexivity |].
  revert i0 t0 v; induction m as [| (i0, t0) m]; intros.
  + simpl. unfold union_pred. simpl. reflexivity.
  + destruct v as [v | v].
    - reflexivity.
    - match goal with
      | _ => apply IHm
      | _ => simpl ; f_equal ; apply IHm
      end.
Qed.

Definition struct_value_fits_aux (m m0: members)
      (P: ListType (map (fun it => reptype (field_type (fst it) m0) -> Prop) m))
      (v: compact_prod (map (fun it => reptype (field_type (fst it) m0)) m)) : Prop.
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
      (P: ListType (map (fun it => reptype (field_type (fst it) m0) -> Prop) m))
      (v: compact_sum (map (fun it => reptype (field_type (fst it) m0)) m)) : Prop.
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
     (fun it => reptype (field_type (fst it) m0) -> Prop)
     P m) v =
  struct_Prop m P v.
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [reflexivity |].
  revert i0 t0 v; induction m as [| (i0, t0) m]; intros.
  + simpl; reflexivity.
  + replace
     (struct_value_fits_aux ((i1, t1) :: (i0, t0) :: m) m0
     (ListTypeGen (fun it : ident * type => reptype (field_type (fst it) m0) -> Prop)
        P ((i1, t1) :: (i0, t0) :: m)) v) with
     (P (i1, t1) (fst v) /\  struct_value_fits_aux ((i0, t0) :: m) m0
     (ListTypeGen (fun it : ident * type => reptype (field_type (fst it) m0) -> Prop)
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
     (fun it => reptype (field_type (fst it) m0) -> Prop)
     P m) v =
  union_Prop m P v.
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [reflexivity |].
  revert i0 t0 v; induction m as [| (i0, t0) m]; intros.
  + simpl. unfold union_Prop. simpl. reflexivity.
  + destruct v as [v | v].
    - reflexivity.
    - match goal with
      | _ => apply IHm
      | _ => simpl ; f_equal ; apply IHm
      end.
Qed.

End AUXILIARY_PRED.

Module auxiliary_pred.

Import aggregate_pred.

Definition struct_data_at_rec_aux:
   forall {cs: compspecs} (sh: share) (m m0: members) (sz: Z) (P: ListType (map (fun it => reptype (field_type (fst it) m0) -> (val -> mpred)) m)) (v: compact_prod (map (fun it => reptype (field_type (fst it) m0)) m)), (val -> mpred)
:= @struct_data_at_rec_aux.

Definition union_data_at_rec_aux:
  forall {cs: compspecs} (sh: share) (m m0: members) (sz: Z) (P: ListType (map (fun it => reptype (field_type (fst it) m0) -> (val -> mpred)) m)) (v: compact_sum (map (fun it => reptype (field_type (fst it) m0)) m)), (val -> mpred)
:= @union_data_at_rec_aux.

Definition struct_data_at_rec_aux_spec: forall {cs: compspecs} (sh: share) m m0 sz v P,
  struct_data_at_rec_aux sh m m0 sz
   (ListTypeGen
     (fun it => reptype (field_type (fst it) m0) -> val -> mpred)
     P m) v =
  struct_pred m
   (fun it v =>
      withspacer sh
       (field_offset cenv_cs (fst it) m0 + sizeof (field_type (fst it) m0))
       (field_offset_next cenv_cs (fst it) m0 sz)
       (at_offset (P it v) (field_offset cenv_cs (fst it) m0))) v
:= @struct_data_at_rec_aux_spec.

Definition union_data_at_rec_aux_spec: forall {cs: compspecs} sh m m0 sz v P,
  union_data_at_rec_aux sh m m0 sz
   (ListTypeGen
     (fun it => reptype (field_type (fst it) m0) -> val -> mpred)
     P m) v =
  union_pred m
   (fun it v =>
      withspacer sh
       (sizeof (field_type (fst it) m0))
       sz
       (P it v)) v
:= @union_data_at_rec_aux_spec.

Definition struct_value_fits_aux:
  forall {cs: compspecs} (m m0: members)
      (P: ListType (map (fun it => reptype (field_type (fst it) m0) -> Prop) m))
      (v: compact_prod (map (fun it => reptype (field_type (fst it) m0)) m)), Prop
:= @struct_value_fits_aux.

Definition union_value_fits_aux:
  forall {cs: compspecs} (m m0: members)
      (P: ListType (map (fun it => reptype (field_type (fst it) m0) -> Prop) m))
      (v: compact_sum (map (fun it => reptype (field_type (fst it) m0)) m)), Prop
:= @union_value_fits_aux.

Definition struct_value_fits_aux_spec: forall {cs: compspecs} m m0 v P,
  struct_value_fits_aux m m0
   (ListTypeGen
     (fun it => reptype (field_type (fst it) m0) -> Prop)
     P m) v =
  struct_Prop m P v
:= @struct_value_fits_aux_spec.

Definition union_value_fits_aux_spec: forall {cs: compspecs} m m0 v P,
  union_value_fits_aux m m0
   (ListTypeGen
     (fun it => reptype (field_type (fst it) m0) -> Prop)
     P m) v =
  union_Prop m P v
:= @union_value_fits_aux_spec.

Definition memory_block_array_pred:
  forall {cs: compspecs} {A : Type} {d : Inhabitant A} (a: A) sh t z b ofs,
  0 <= z ->
  0 <= ofs /\ ofs + sizeof t * z < Ptrofs.modulus ->
  array_pred 0 z
     (fun i _ p =>
      memory_block sh (sizeof t)
        (offset_val (sizeof t * i) p)) (list_repeat (Z.to_nat z) a)
     (Vptr b (Ptrofs.repr ofs))  =
  memory_block sh (sizeof t * z) (Vptr b (Ptrofs.repr ofs))
:= @memory_block_array_pred'.

Definition memory_block_struct_pred:
  forall {cs: compspecs} sh m sz {A} (v: compact_prod (map A m)) b ofs,
  (m = nil -> sz = 0) ->
  members_no_replicate m = true ->
  sizeof_struct cenv_cs 0 m <= sz < Ptrofs.modulus ->
  0 <= ofs /\ ofs + sz < Ptrofs.modulus ->
  struct_pred m
   (fun it _ p =>
     (memory_block sh (field_offset_next cenv_cs (fst it) m sz - field_offset cenv_cs (fst it) m))
     (offset_val (field_offset cenv_cs (fst it) m) p)) v (Vptr b (Ptrofs.repr ofs)) =
  memory_block sh sz (Vptr b (Ptrofs.repr ofs))
:= @memory_block_struct_pred.

Definition memory_block_union_pred:
  forall sh m sz {A} (v: compact_sum (map A m)) b ofs,
  (m = nil -> sz = 0) ->
  union_pred m (fun it _ => memory_block sh sz) v (Vptr b (Ptrofs.repr ofs)) =
  memory_block sh sz (Vptr b (Ptrofs.repr ofs))
:= @memory_block_union_pred.

End auxiliary_pred.
