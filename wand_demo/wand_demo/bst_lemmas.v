Require Import VST.floyd.proofauto.
Require Import VFA.Maps.
Require Import VFA.SearchTree.
Require Import WandDemo.SearchTree_ext.
Require Import WandDemo.wand_frame.
Require Import WandDemo.wandQ_frame.
Require Import WandDemo.wandQ_frame_tactic.
Require Import WandDemo.bst.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition t_struct_tree := Tstruct _tree noattr.

Fixpoint tree_rep (t: tree val) (p: val) : mpred :=
 match t with
 | E => !!(p=nullval) && emp
 | T a x v b => !! (Int.min_signed <= Z.of_nat x <= Int.max_signed /\ tc_val (tptr Tvoid) v) &&
    EX pa:val, EX pb:val,
    data_at Tsh t_struct_tree (Vint (Int.repr (Z.of_nat x)),(v,(pa,pb))) p *
    tree_rep a pa * tree_rep b pb
 end.

Definition treebox_rep (t: tree val) (b: val) :=
 EX p: val, data_at Tsh (tptr t_struct_tree) p b * tree_rep t p.

Lemma tree_rep_spec: forall (t: tree val) (p: val),
  tree_rep t p =
  match t with
  | E => !!(p=nullval) && emp
  | T a x v b => !! (Int.min_signed <= Z.of_nat x <= Int.max_signed /\ tc_val (tptr Tvoid) v) &&
     EX pa:val, EX pb:val,
     data_at Tsh t_struct_tree (Vint (Int.repr (Z.of_nat x)),(v,(pa,pb))) p *
     tree_rep a pa * tree_rep b pb
  end.
Proof.
  intros.
  destruct t; auto.
Qed.

Lemma treebox_rep_spec: forall (t: tree val) (b: val),
  treebox_rep t b =
  EX p: val,
  data_at Tsh (tptr t_struct_tree) p b *
  match t with
  | E => !!(p=nullval) && emp
  | T l x v r => !! (Int.min_signed <= Z.of_nat x <= Int.max_signed /\ tc_val (tptr Tvoid) v) &&
      field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr (Z.of_nat x))) p *
      field_at Tsh t_struct_tree [StructField _value] v p *
      treebox_rep l (field_address t_struct_tree [StructField _left] p) *
      treebox_rep r (field_address t_struct_tree [StructField _right] p)
  end.
Proof.
  intros.
  unfold treebox_rep at 1.
  f_equal.
  extensionality p.
  destruct t; simpl.
  + apply pred_ext; entailer!.
  + unfold treebox_rep.
    apply pred_ext; entailer!.
    - Intros pa pb.
      Exists pb pa.
      unfold_data_at (data_at _ _ _ p).
      rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
      rewrite (field_at_data_at _ t_struct_tree [StructField _right]).
      cancel.
    - Intros pa pb.
      Exists pb pa.
      unfold_data_at (data_at _ _ _ p).
      rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
      rewrite (field_at_data_at _ t_struct_tree [StructField _right]).
      cancel.
Qed.

Lemma treebox_rep_tree_rep: forall (t: tree val) (b: val),
  treebox_rep t b = EX p: val, data_at Tsh (tptr t_struct_tree) p b * tree_rep t p.
Proof.
  intros.
  reflexivity.
Qed.

Lemma tree_rep_treebox_rep: forall (t: tree val) (p: val),
  tree_rep t p =
  match t with
  | E => !!(p=nullval) && emp
  | T l x v r => !! (Int.min_signed <= Z.of_nat x <= Int.max_signed /\ tc_val (tptr Tvoid) v) &&
      field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr (Z.of_nat x))) p *
      field_at Tsh t_struct_tree [StructField _value] v p *
      treebox_rep l (field_address t_struct_tree [StructField _left] p) *
      treebox_rep r (field_address t_struct_tree [StructField _right] p)
  end.
Proof.
  intros.
  destruct t; auto.
  unfold treebox_rep; simpl.
  apply pred_ext; Intros pa pb.
  + Exists pb pa; entailer!.
    unfold_data_at (data_at _ _ _ p).
    cancel.
  + Exists pb pa; entailer!.
    unfold_data_at (data_at _ _ _ p).
    cancel.
Qed.

Arguments tree_rep: simpl never.
Arguments treebox_rep: simpl never.
Opaque treebox_rep tree_rep.

Lemma tree_rep_saturate_local:
   forall t p, tree_rep t p |-- !! is_pointer_or_null p.
Proof.
  intros.
  rewrite tree_rep_treebox_rep.
  destruct t;
  entailer!.
Qed.

Hint Resolve tree_rep_saturate_local: saturate_local.

Lemma tree_rep_valid_pointer:
  forall t p, tree_rep t p |-- valid_pointer p.
Proof.
  intros.
  rewrite tree_rep_treebox_rep.
  destruct t; simpl;
   normalize;
   auto with valid_pointer.
  repeat apply sepcon_valid_pointer1.
  apply field_at_valid_ptr0; auto.
  reflexivity.
Qed.
Hint Resolve tree_rep_valid_pointer: valid_pointer.

Lemma treebox_rep_saturate_local:
   forall t b, treebox_rep t b |-- !! field_compatible (tptr t_struct_tree) [] b.
Proof.
intros.
rewrite treebox_rep_spec.
Intros p.
destruct t;
entailer!.
Qed.

Hint Resolve treebox_rep_saturate_local: saturate_local.

Lemma tree_rep_nullval: forall t,
  tree_rep t nullval |-- !! (t = E).
Proof.
  intros.
  destruct t; [entailer! |].
  rewrite tree_rep_treebox_rep.
  entailer!.
Qed.

Hint Resolve tree_rep_nullval: saturate_local.

Lemma treebox_rep_leaf: forall x p b (v: val),
  is_pointer_or_null v ->
  Int.min_signed <= Z.of_nat x <= Int.max_signed ->
  data_at Tsh t_struct_tree (Vint (Int.repr (Z.of_nat x)), (v, (nullval, nullval))) p * data_at Tsh (tptr t_struct_tree) p b |-- treebox_rep (T E x v E) b.
Proof.
  intros.
  rewrite treebox_rep_spec.
  Exists p.
  rewrite !treebox_rep_spec.
  Exists nullval nullval.
  unfold_data_at (data_at _ _ _ p).
  entailer!.
Qed.

Lemma treebox_rep_internal: forall l x v r b p,
  Int.min_signed <= Z.of_nat x <= Int.max_signed ->
  tc_val (tptr Tvoid) v ->
  data_at Tsh (tptr t_struct_tree) p b *
  field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr (Z.of_nat x))) p *
  field_at Tsh t_struct_tree [StructField _value] v p *
  treebox_rep l (field_address t_struct_tree [StructField _left] p) *
  treebox_rep r (field_address t_struct_tree [StructField _right] p) |--
  treebox_rep (T l x v r) b.
Proof.
  intros.
  rewrite (treebox_rep_spec (T _ _ _ _)).
  Exists p.
  entailer!.
Qed.

Lemma tree_rep_internal: forall l x v r (p p1 p2: val),
  Int.min_signed <= Z.of_nat x <= Int.max_signed ->
  tc_val (tptr Tvoid) v ->
  data_at Tsh t_struct_tree (Vint (Int.repr (Z.of_nat x)), (v, (p1, p2))) p *
  tree_rep l p1 *
  tree_rep r p2 |--
  tree_rep (T l x v r) p.
Proof.
  intros.
  rewrite (tree_rep_spec (T _ _ _ _)).
  Exists p1 p2.
  entailer!.
Qed.

Module PartialTree_WandQFrame_Func_Hole.

Definition partialT (rep: tree val -> val -> mpred) (P: tree val -> tree val) (p_root p_in: val): mpred :=
  ALL t: tree val, rep t p_in -* rep (P t) p_root.

Lemma partialT_rep_partialT_rep: forall rep pt12 pt23 p1 p2 p3,
  partialT rep pt12 p2 p1 * partialT rep pt23 p3 p2 |-- partialT rep (Basics.compose pt23 pt12) p3 p1.
Proof.
  intros.
  unfold partialT.
  sep_apply (wandQ_frame_refine _ _ (fun t => rep t p2 -* rep (pt23 t) p3) pt12).
  rewrite sepcon_comm.
  apply wandQ_frame_ver.
Qed.

Lemma partialT_rep_partialT_rep_proof_by_tactic: forall rep pt12 pt23 p1 p2 p3,
  partialT rep pt12 p2 p1 * partialT rep pt23 p3 p2 |-- partialT rep (Basics.compose pt23 pt12) p3 p1.
Proof.
  intros.
  solve_wandQ partialT.
  simpl; auto.
Qed.

Lemma emp_partialT_rep_H: forall rep p,
  emp |-- partialT rep (fun t => t) p p.
Proof.
  intros.
  apply allp_right; intros.
  apply wand_sepcon_adjoint.
  normalize.
Qed.

Lemma rep_partialT_rep: forall rep t P p q,
  rep t p * partialT rep P q p |-- rep (P t) q.
Proof.
  intros.
  exact (wandQ_frame_elim _ (fun t => rep t p) (fun t => rep (P t) q) t).
Qed.

Lemma rep_partialT_rep_proof_by_tactic: forall rep t P p q,
  rep t p * partialT rep P q p |-- rep (P t) q.
Proof.
  intros.
  solve_wandQ partialT.
  simpl; auto.
Qed.

End PartialTree_WandQFrame_Func_Hole.

Module PartialTreeboxRep_WandQFrame_Func_Hole.

Export PartialTree_WandQFrame_Func_Hole.

Definition partial_treebox_rep := partialT treebox_rep.

Lemma partial_treebox_rep_singleton_left: forall (t2: tree val) k (v p b: val),
  Int.min_signed <= Z.of_nat k <= Int.max_signed ->
  is_pointer_or_null v ->
  data_at Tsh (tptr t_struct_tree) p b *
  field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr (Z.of_nat k))) p *
  field_at Tsh t_struct_tree [StructField _value] v p *
  treebox_rep t2 (field_address t_struct_tree [StructField _right] p)
  |-- partial_treebox_rep (fun t1 => T t1 k v t2) b (field_address t_struct_tree [StructField _left] p).
Proof.
  intros.
  unfold partial_treebox_rep, partialT.
  apply allp_right; intros t1.
  rewrite <- wand_sepcon_adjoint.
  rewrite (treebox_rep_spec (T t1 k v t2)).
  Exists p.
  entailer!.
Qed.

Lemma partial_treebox_rep_singleton_right: forall (t1: tree val) k (v p b: val),
  Int.min_signed <= Z.of_nat k <= Int.max_signed ->
  is_pointer_or_null v ->
  data_at Tsh (tptr t_struct_tree) p b *
  field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr (Z.of_nat k))) p *
  field_at Tsh t_struct_tree [StructField _value] v p *
  treebox_rep t1 (field_address t_struct_tree [StructField _left] p)
  |-- partial_treebox_rep (fun t2 => T t1 k v t2) b (field_address t_struct_tree [StructField _right] p).
Proof.
  intros.
  unfold partial_treebox_rep, partialT.
  apply allp_right; intros t2.
  rewrite <- wand_sepcon_adjoint.
  rewrite (treebox_rep_spec (T t1 k v t2)).
  Exists p.
  entailer!.
Qed.

Lemma partial_treebox_rep_partial_treebox_rep: forall pt12 pt23 p1 p2 p3,
  partial_treebox_rep pt12 p2 p1 * partial_treebox_rep pt23 p3 p2 |-- partial_treebox_rep (Basics.compose pt23 pt12) p3 p1.
Proof. apply partialT_rep_partialT_rep. Qed.

Lemma emp_partial_treebox_rep_H: forall p,
  emp |-- partial_treebox_rep (fun t => t) p p.
Proof. apply emp_partialT_rep_H. Qed.

Lemma treebox_rep_partial_treebox_rep: forall t pt p q,
  treebox_rep t p * partial_treebox_rep pt q p |-- treebox_rep (pt t) q.
Proof. apply rep_partialT_rep. Qed.

End PartialTreeboxRep_WandQFrame_Func_Hole.

Module PartialTreeboxRep_WandFrame.

Lemma partial_treebox_rep_singleton_left: forall (t1' t2: tree val) k (v p b: val),
  Int.min_signed <= Z.of_nat k <= Int.max_signed ->
  is_pointer_or_null v ->
  data_at Tsh (tptr t_struct_tree) p b *
  field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr (Z.of_nat k))) p *
  field_at Tsh t_struct_tree [StructField _value] v p *
  treebox_rep t2 (field_address t_struct_tree [StructField _right] p)
  |-- treebox_rep t1'
        (field_address t_struct_tree [StructField _left] p) -*
      treebox_rep (T t1' k v t2) b.
Proof.
  intros.
  rewrite (treebox_rep_spec (T t1' k v t2)).
  rewrite <- wand_sepcon_adjoint.
  Exists p.
  entailer!.
Qed.

Lemma partial_treebox_rep_singleton_right: forall (t1 t2': tree val) k (v p b: val),
  Int.min_signed <= Z.of_nat k <= Int.max_signed ->
  is_pointer_or_null v ->
  data_at Tsh (tptr t_struct_tree) p b *
  field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr (Z.of_nat k))) p *
  field_at Tsh t_struct_tree [StructField _value] v p *
  treebox_rep t1 (field_address t_struct_tree [StructField _left] p)
  |-- treebox_rep t2'
       (field_address t_struct_tree [StructField _right] p) -*
      treebox_rep (T t1 k v t2') b.
Proof.
  intros.
  rewrite (treebox_rep_spec (T t1 k v t2')).
  rewrite <- wand_sepcon_adjoint.
  Exists p.
  entailer!.
Qed.

Lemma partial_treebox_rep_partial_treebox_rep: forall t1 t2 t3 p1 p2 p3,
  (treebox_rep t1 p1 -* treebox_rep t2 p2) * (treebox_rep t2 p2 -* treebox_rep t3 p3) |-- treebox_rep t1 p1 -* treebox_rep t3 p3.
Proof.
  intros.
  apply wand_frame_ver.
Qed.

Lemma emp_partial_treebox_rep_H: forall t p,
  emp |-- treebox_rep t p -* treebox_rep t p.
Proof.
  intros.
  apply wand_sepcon_adjoint.
  normalize.
Qed.

Lemma treebox_rep_partial_treebox_rep: forall t t0 p p0,
  treebox_rep t p * (treebox_rep t p -* treebox_rep t0 p0) |-- treebox_rep t0 p0.
Proof.
  intros.
  apply modus_ponens_wand.
Qed.

End PartialTreeboxRep_WandFrame.

Module PartialTreeboxRep_WandQFrame_Ind_Hole.

Definition partial_treebox_rep (pt: partial_tree val) (p_root p_in: val): mpred :=
  ALL t: tree val, treebox_rep t p_in -* treebox_rep (partial_tree_tree pt t) p_root.

Lemma partial_treebox_rep_singleton_left: forall (t2: tree val) k (v p b: val),
  Int.min_signed <= Z.of_nat k <= Int.max_signed ->
  is_pointer_or_null v ->
  data_at Tsh (tptr t_struct_tree) p b *
  field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr (Z.of_nat k))) p *
  field_at Tsh t_struct_tree [StructField _value] v p *
  treebox_rep t2 (field_address t_struct_tree [StructField _right] p)
  |-- partial_treebox_rep (L H k v t2) b (field_address t_struct_tree [StructField _left] p).
Proof.
  intros.
  unfold partial_treebox_rep.
  apply allp_right; intros t1.
  rewrite <- wand_sepcon_adjoint.
  rewrite (treebox_rep_spec (T t1 k v t2)).
  Exists p.
  entailer!.
Qed.

Lemma partial_treebox_rep_singleton_right: forall (t1: tree val) k (v p b: val),
  Int.min_signed <= Z.of_nat k <= Int.max_signed ->
  is_pointer_or_null v ->
  data_at Tsh (tptr t_struct_tree) p b *
  field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr (Z.of_nat k))) p *
  field_at Tsh t_struct_tree [StructField _value] v p *
  treebox_rep t1 (field_address t_struct_tree [StructField _left] p)
  |-- partial_treebox_rep (R t1 k v H) b (field_address t_struct_tree [StructField _right] p).
Proof.
  intros.
  unfold partial_treebox_rep.
  apply allp_right; intros t2.
  rewrite <- wand_sepcon_adjoint.
  rewrite (treebox_rep_spec (T t1 k v t2)).
  Exists p.
  entailer!.
Qed.

Lemma partial_treebox_rep_partial_treebox_rep: forall pt12 pt23 p1 p2 p3,
  partial_treebox_rep pt12 p2 p1 * partial_treebox_rep pt23 p3 p2 |-- partial_treebox_rep (partial_tree_partial_tree pt23 pt12) p3 p1.
Proof.
  intros.
  unfold partial_treebox_rep.
  rewrite partial_tree_partial_tree_tree.
  sep_apply (wandQ_frame_refine _ _ (fun t => treebox_rep t p2 -* treebox_rep (partial_tree_tree pt23 t) p3) (partial_tree_tree pt12)).
  rewrite sepcon_comm.
  apply wandQ_frame_ver.
Qed.

Lemma emp_partial_treebox_rep_H: forall p,
  emp |-- partial_treebox_rep SearchTree_ext.H p p.
Proof.
  intros.
  apply allp_right; intros.
  apply wand_sepcon_adjoint.
  normalize.
  simpl.
  auto.
Qed.

Lemma treebox_rep_partial_treebox_rep: forall t pt p q,
  treebox_rep t p * partial_treebox_rep pt q p |-- treebox_rep (partial_tree_tree pt t) q.
Proof.
  intros.
  unfold partial_treebox_rep.
  change (treebox_rep (partial_tree_tree pt t) q)
    with ((fun t => treebox_rep (partial_tree_tree pt t) q) t).
  change (treebox_rep t p)
    with ((fun t => treebox_rep t p) t).
  apply wandQ_frame_elim.
Qed.

End PartialTreeboxRep_WandQFrame_Ind_Hole.

Module PartialTreeboxRep_Ind_Pred_Ind_Hole.

Fixpoint partial_treebox_rep (pt: partial_tree val) (p_root p_in: val): mpred :=
  match pt with
  | H => !! (p_root = p_in) && emp
  | L pt1 x v t2 =>
      EX p : val,
        !! (Int.min_signed <= Z.of_nat x <= Int.max_signed /\ tc_val (tptr Tvoid) v) &&
        data_at Tsh (tptr t_struct_tree) p p_root *
        field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr (Z.of_nat x))) p *
        field_at Tsh t_struct_tree [StructField _value] v p *
        partial_treebox_rep pt1 (field_address t_struct_tree [StructField _left] p) p_in *
        treebox_rep t2 (field_address t_struct_tree [StructField _right] p)
  | R t1 x v pt2 =>
      EX p : val,
        !! (Int.min_signed <= Z.of_nat x <= Int.max_signed /\ tc_val (tptr Tvoid) v) &&
        data_at Tsh (tptr t_struct_tree) p p_root *
        field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr (Z.of_nat x))) p *
        field_at Tsh t_struct_tree [StructField _value] v p *
        treebox_rep t1 (field_address t_struct_tree [StructField _left] p) *
        partial_treebox_rep pt2 (field_address t_struct_tree [StructField _right] p) p_in
  end.

Lemma partial_treebox_rep_singleton_left: forall (t2: tree val) k (v p b: val),
  Int.min_signed <= Z.of_nat k <= Int.max_signed ->
  is_pointer_or_null v ->
  data_at Tsh (tptr t_struct_tree) p b *
  field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr (Z.of_nat k))) p *
  field_at Tsh t_struct_tree [StructField _value] v p *
  treebox_rep t2 (field_address t_struct_tree [StructField _right] p)
  |-- partial_treebox_rep (L H k v t2) b (field_address t_struct_tree [StructField _left] p).
Proof.
  intros.
  unfold partial_treebox_rep.
  Exists p.
  entailer!.
Qed.

Lemma partial_treebox_rep_singleton_right: forall (t1: tree val) k (v p b: val),
  Int.min_signed <= Z.of_nat k <= Int.max_signed ->
  is_pointer_or_null v ->
  data_at Tsh (tptr t_struct_tree) p b *
  field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr (Z.of_nat k))) p *
  field_at Tsh t_struct_tree [StructField _value] v p *
  treebox_rep t1 (field_address t_struct_tree [StructField _left] p)
  |-- partial_treebox_rep (R t1 k v H) b (field_address t_struct_tree [StructField _right] p).
Proof.
  intros.
  unfold partial_treebox_rep.
  Exists p.
  entailer!.
Qed.

Lemma partial_treebox_rep_partial_treebox_rep: forall pt12 pt23 p1 p2 p3,
  partial_treebox_rep pt12 p2 p1 * partial_treebox_rep pt23 p3 p2 |-- partial_treebox_rep (partial_tree_partial_tree pt23 pt12) p3 p1.
Proof.
  intros.
  revert p3; induction pt23; intros.
  + simpl.
    entailer!.
  + simpl.
    Intros p.
    Exists p.
    entailer!.
    apply IHpt23.
  + simpl.
    Intros p.
    Exists p.
    entailer!.
    apply IHpt23.
Qed.

Lemma emp_partial_treebox_rep_H: forall p,
  emp |-- partial_treebox_rep H p p.
Proof.
  intros.
  unfold partial_treebox_rep.
  entailer!.
Qed.

Lemma treebox_rep_partial_treebox_rep: forall t pt p q,
  treebox_rep t p * partial_treebox_rep pt q p |-- treebox_rep (partial_tree_tree pt t) q.
Proof.
  intros.
  revert q; induction pt; intros.
  + simpl.
    entailer!.
  + simpl.
    Intros p'.
    rewrite (treebox_rep_spec (T (partial_tree_tree pt t) k v t0)).
    Exists p'.
    entailer!.
    apply IHpt.
  + simpl.
    Intros p'.
    rewrite (treebox_rep_spec (T t0 k v (partial_tree_tree pt t))).
    Exists p'.
    entailer!.
    apply IHpt.
Qed.

End PartialTreeboxRep_Ind_Pred_Ind_Hole.

Module PartialTreeRep_WandQFrame_Func_Hole.

Export PartialTree_WandQFrame_Func_Hole.

Definition partial_tree_rep := partialT tree_rep.

Lemma partial_tree_rep_singleton_left: forall (t2: tree val) k (v p p1 p2: val),
  Int.min_signed <= Z.of_nat k <= Int.max_signed ->
  is_pointer_or_null v ->
  data_at Tsh t_struct_tree (Vint (Int.repr (Z.of_nat k)), (v, (p1, p2))) p *
  tree_rep t2 p2
  |-- partial_tree_rep (fun t1 => T t1 k v t2) p p1.
Proof.
  intros.
  unfold partial_tree_rep, partialT.
  apply allp_right; intros t1.
  rewrite <- wand_sepcon_adjoint.
  rewrite (tree_rep_spec (T t1 k v t2)).
  Exists p1 p2.
  entailer!.
Qed.

Lemma partial_tree_rep_singleton_right: forall (t1: tree val) k (v p p1 p2: val),
  Int.min_signed <= Z.of_nat k <= Int.max_signed ->
  is_pointer_or_null v ->
  data_at Tsh t_struct_tree (Vint (Int.repr (Z.of_nat k)), (v, (p1, p2))) p *
  tree_rep t1 p1
  |-- partial_tree_rep (fun t2 => T t1 k v t2) p p2.
Proof.
  intros.
  unfold partial_tree_rep, partialT.
  apply allp_right; intros t2.
  rewrite <- wand_sepcon_adjoint.
  rewrite (tree_rep_spec (T t1 k v t2)).
  Exists p1 p2.
  entailer!.
Qed.

Lemma partial_tree_rep_partial_tree_rep: forall pt12 pt23 p1 p2 p3,
  partial_tree_rep pt12 p2 p1 * partial_tree_rep pt23 p3 p2 |-- partial_tree_rep (Basics.compose pt23 pt12) p3 p1.
Proof. apply partialT_rep_partialT_rep. Qed.

Lemma emp_partial_tree_rep_H: forall p,
  emp |-- partial_tree_rep (fun t => t) p p.
Proof. apply emp_partialT_rep_H. Qed.

Lemma tree_rep_partial_tree_rep: forall t pt p q,
  tree_rep t p * partial_tree_rep pt q p |-- tree_rep (pt t) q.
Proof. apply rep_partialT_rep. Qed.

End PartialTreeRep_WandQFrame_Func_Hole.

Definition Map_rep (m: total_map val) (p: val): mpred :=
  EX t: tree val, !! (Abs val nullval t m /\ SearchTree val t) && tree_rep t p.

Definition Mapbox_rep (m: total_map val) (p: val): mpred :=
  EX q: val, data_at Tsh (tptr t_struct_tree) q p * Map_rep m q.

Lemma Mapbox_rep_unfold: forall (m: total_map val) (p: val),
  Mapbox_rep m p = EX t: tree val, !! (Abs val nullval t m /\ SearchTree val t) && treebox_rep t p.
Proof.
  intros.
  apply pred_ext.
  + unfold Mapbox_rep, Map_rep; Intros q t.
    Exists t.
    rewrite treebox_rep_tree_rep.
    Exists q.
    entailer!.
  + Intros t.
    rewrite treebox_rep_tree_rep.
    Intros q.
    unfold Mapbox_rep, Map_rep; Exists q t.
    entailer!.
Qed.

Opaque Map_rep.
Arguments Map_rep: simpl never.
