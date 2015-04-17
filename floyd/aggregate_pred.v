Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.type_induction.
Require Import floyd.fieldlist.
Require Import floyd.nested_field_lemmas.
Require Import floyd.mapsto_memory_block.
Require Import floyd.rangespec_lemmas.
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

Definition struct_pred (m: members) (A: ident * type -> Type) (P: forall it, A it -> val -> mpred) (v: compact_prod (map A m)): val -> mpred.
Proof.
  destruct m as [| (i0, t0) m]; [exact (fun _ => emp) |].
  revert i0 t0 v; induction m as [| (i0, t0) m]; intros ? ? v.
  + simpl in v.
    exact (P _ v).
  + simpl in v.
    exact ((P _ (fst v)) * IHm i0 t0 (snd v)).
Defined.

(* when unfold, do cbv [struct_pred list_rect]. *)

Definition union_pred (m: members) (A: ident * type -> Type) (P: forall it, A it -> val -> mpred) (v: compact_sum (map A m)): val -> mpred.
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
    rewrite at_offset_eq.
    pose_size_mult cenv_cs t (0 :: hi - Z.succ lo :: hi - lo :: nil).
    rewrite IHn; [| apply arith_aux02; auto | omega | omega | omega].
    replace (ofs + sizeof cenv_cs t * Z.succ lo) with (ofs + sizeof cenv_cs t * lo + sizeof cenv_cs t) by omega.
    unfold offset_val.
    solve_mod_modulus.
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

Lemma members_no_replicate_ind: forall m,
  (members_no_replicate m = true) <->
  match m with
  | nil => True
  | (i0, _) :: m0 => ~ in_members i0 m0 /\ members_no_replicate m0 = true
  end.
Proof.
  intros.
  unfold members_no_replicate.
  destruct m as [| [i t] m]; simpl.
  + assert (true = true) by auto; tauto.
  + destruct (id_in_list i (map fst m)) eqn:HH.
    - apply id_in_list_true in HH.
      assert (~ false = true) by congruence; tauto.
    - apply id_in_list_false in HH.
      tauto.
Qed.

Lemma struct_pred_ext_derives: forall m {A} (d: forall it, A it) (P0 P1: forall it, A it -> val -> mpred) v0 v1 p,
  members_no_replicate m = true ->
  (forall i, in_members i m ->
     P0 _ (proj_struct i m v0 (d _)) p |-- P1 _ (proj_struct i m v1 (d _)) p) ->
  struct_pred m A P0 v0 p |-- struct_pred m A P1 v1 p.
Proof.
  unfold field_type2.
  intros.
  destruct m as [| (i0, t0) m]; [simpl; auto |].
  revert i0 t0 v0 v1 H H0; induction m as [| (i1, t1) m]; intros.
  + specialize (H0 i0).
    spec H0; [left; reflexivity |].
    simpl in H0.
    if_tac in H0; [| congruence].
    unfold eq_rect_r in H0; rewrite <- !eq_rect_eq in H0.
    simpl.
    exact H0.
  + change (struct_pred ((i0, t0) :: (i1, t1) :: m) A P0 v0 p) with
      (P0 (i0, t0) (fst v0) p * struct_pred ((i1, t1) :: m) A P0 (snd v0) p).
    change (struct_pred ((i0, t0) :: (i1, t1) :: m) A P1 v1 p) with
      (P1 (i0, t0) (fst v1) p * struct_pred ((i1, t1) :: m) A P1 (snd v1) p).
    apply sepcon_derives.
    - specialize (H0 i0).
      spec H0; [left; reflexivity |].
      simpl in H0.
      if_tac in H0; [| congruence].
      unfold eq_rect_r in H0; rewrite <- !eq_rect_eq in H0.
      simpl.
      exact H0.
    - rewrite members_no_replicate_ind in H.
      apply IHm; [tauto |].
      intros.
      specialize (H0 i).
      spec H0; [right; auto |].
      simpl in H0.
      if_tac in H0.
      * clear - H H1 H2.
        subst.
        tauto.
      * exact H0.
Qed.


struct_pred (m: members) (A: ident * type -> Type) (P: forall it, A it -> val -> mpred) (v: compact_prod (map A m)): val -> mpred.
Import floyd.fieldlist.fieldlist.
