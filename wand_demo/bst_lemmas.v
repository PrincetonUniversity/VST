Require Import VST.floyd.proofauto.
Require Import VFA.SearchTree.
Require Import WandDemo.SearchTree_ext.
Require Import WandDemo.wand_frame.
Require Import WandDemo.wandQ_frame.
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
      unfold_data_at 1%nat.
      rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
      rewrite (field_at_data_at _ t_struct_tree [StructField _right]).
      cancel.
    - Intros pa pb.
      Exists pb pa.
      unfold_data_at 3%nat.
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
    unfold_data_at 1%nat.
    cancel.
    rewrite !field_at_data_at.
    cancel.
  + Exists pb pa; entailer!.
    unfold_data_at 3%nat.
    cancel.
    rewrite !field_at_data_at.
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
  unfold_data_at 1%nat.
  entailer!.
  rewrite !field_at_data_at.
  cancel.
Qed.

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

Module PartialTreeboxRep_WandQFrame.

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

End PartialTreeboxRep_WandQFrame.
