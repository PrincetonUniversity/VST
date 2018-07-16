Require Import VST.floyd.proofauto.
Require Import VFA.Maps.
Require Import VFA.SearchTree.
Require Import WandDemo.SearchTree_ext.
Require Import WandDemo.bst.
Require Import WandDemo.bst_lemmas.
Require Import WandDemo.VST_lemmas.
Require Import WandDemo.spec_bst.

Lemma if_trueb: forall {A: Type} b (a1 a2: A), b = true -> (if b then a1 else a2) = a1.
Proof. intros; subst; auto. Qed.

Lemma if_falseb: forall {A: Type} b (a1 a2: A), b = false -> (if b then a1 else a2) = a2.
Proof. intros; subst; auto. Qed.

Ltac simpl_compb := first [ rewrite if_trueb by (apply NPeano.Nat.ltb_lt; rewrite Nat2Z.inj_lt; omega)
                          | rewrite if_falseb by (apply NPeano.Nat.ltb_nlt; rewrite Nat2Z.inj_lt; omega)].

Import PartialTreeRep_WandQFrame_Func_Hole.

Definition lookup_inv (p0: val) (t0: tree val) (x: nat): environ -> mpred :=
  EX p: val, EX t: tree val, EX P: tree val -> tree val,
  PROP(lookup nullval x t = lookup nullval x t0; P t = t0)
  LOCAL(temp _p p; temp _x (Vint (Int.repr (Z.of_nat x))))
  SEP(tree_rep t p; partial_tree_rep P p0 p).

Opaque tree_rep.
Arguments tree_rep: simpl never.

Lemma body_lookup: semax_body Vprog Gprog f_lookup lookup_spec.
Proof.
  start_function.
  unfold Map_rep.
  Intros t0.
  apply (semax_post'' (PROP () LOCAL (temp ret_temp (lookup nullval x t0)) SEP (tree_rep t0 p0))); auto.
  {
    unfold Map_rep.
    Exists t0.
    entailer!.
    symmetry; apply lookup_relate; auto.
  }
  clear H0 H1.
  forward_while (lookup_inv p0 t0 x).
  * (* precondition implies loop invariant *)
    Exists p0 t0 (fun t: tree val => t). entailer!.
    apply emp_partial_tree_rep_H.
  * (* type-check loop condition *)
    entailer!.
  * (* loop body preserves invariant *)
    destruct t; rewrite tree_rep_spec at 1. normalize.
    Intros qa qb.
    forward.
    forward_if; [ | forward_if ].
    + (* then clause: x<y *)
      forward. (* q=q<-left *)
      Exists (qa, t1, fun t1 => P (T t1 k v0 t2)). unfold fst,snd.
      entailer!.
      - rewrite <- H0; simpl.
        simpl_compb; auto.
      - sep_apply (partial_tree_rep_singleton_left t2 k v0 p qa qb); auto.
        apply partial_tree_rep_partial_tree_rep.
    + (* else-then clause: y<x *)
      forward. (* q=q<-right *)
      Exists (qb,t2, fun t2 => P (T t1 k v0 t2)). unfold fst,snd.
      entailer!.
      - rewrite <- H0; simpl.
        simpl_compb; simpl_compb; auto.
      - sep_apply (partial_tree_rep_singleton_right t1 k v0 p qa qb); auto.
        apply partial_tree_rep_partial_tree_rep.
    + (* else-else clause: x=y *)
      assert (x=k) by omega. subst x. clear H H4 H5.
      forward. (* v=q->value *)
      forward. (* return v; *)
      entailer!.
      - rewrite <- H0; simpl.
        simpl_compb; simpl_compb; auto.
      - sep_apply (tree_rep_internal t1 k v0 t2 p qa qb); auto.
        apply tree_rep_partial_tree_rep.
  * (* after the loop *)
    forward. (* return NULL; *)
    entailer!.
    apply tree_rep_partial_tree_rep.
Qed.

Lemma body_turn_left: semax_body Vprog Gprog f_turn_left turn_left_spec.
Proof.
  start_function.
  rewrite (tree_rep_spec (T _ _ _ _)).
  Intros pb pc.
  forward. (* mid=r->left *)
  forward. (* l->right=mid *)
  assert_PROP (is_pointer_or_null pb) by entailer!.
  rewrite is_pointer_or_null_force_val_sem_cast_neutral by auto.
  forward. (* r->left=l *)
  assert_PROP (is_pointer_or_null l) by entailer!.
  rewrite is_pointer_or_null_force_val_sem_cast_neutral by auto.
  forward. (* _l = r *)
  assert_PROP (is_pointer_or_null r) by entailer!.
  rewrite is_pointer_or_null_force_val_sem_cast_neutral by auto.
  forward. (* return *)
  (* TODO: simplify the following proof *)
  Exists pc.
  entailer!.
  rewrite (tree_rep_spec (T _ _ _ _)).
  Exists pa pb.
  entailer!.
Qed.

Import PartialTreeboxRep_WandQFrame_Func_Hole.

Definition pushdown_left_inv (b_res: val) (t_res: tree val): environ -> mpred :=
  EX b: val, EX ta: tree val, EX x: nat, EX v: val, EX tb: tree val, EX P: tree val -> tree val,
  PROP  (P (pushdown_left ta tb) = t_res)
  LOCAL (temp _t b)
  SEP   (treebox_rep (T ta x v tb) b; partial_treebox_rep P b_res b).

Lemma body_pushdown_left: semax_body Vprog Gprog f_pushdown_left pushdown_left_spec.
Proof.
  start_function.
  forward_loop (pushdown_left_inv b (pushdown_left ta tb)).
  + (* Precondition *)
    unfold pushdown_left_inv.
    Exists b ta x v tb (fun t: tree val => t).
    entailer!.
    sep_apply (treebox_rep_internal ta x v tb b p); auto.
    entailer!.
    apply emp_partial_treebox_rep_H.
  + (* Loop body *)
    unfold pushdown_left_inv.
    clear x v H H0.
    Intros b0 ta0 x vx tbc0 P.
    rewrite treebox_rep_tree_rep.
    Intros p0.
    forward. (* p = *t; *)
    rewrite tree_rep_spec.
    Intros pa pbc.
    forward. (* q = p->right *)
    forward_if.
    - subst.
      assert_PROP (tbc0 = (@E _)).
        1: entailer!.
      subst.
      forward. (* q=p->left *)
      forward. (* *t=q *)
      forward_call (p0, sizeof t_struct_tree). (* freeN(p, sizeof ( *p )); *)
      Focus 1. {
        entailer!.
        rewrite memory_block_data_at_ by auto.
        cancel.
      } Unfocus.
      forward. (* return *)
      rewrite (tree_rep_spec E).
      rewrite <- H.
      eapply derives_trans; [| apply (treebox_rep_partial_treebox_rep _ _ b0)].
      entailer!.
      simpl.
      rewrite treebox_rep_tree_rep.
      Exists pa.
      cancel.
    - destruct tbc0 as [| tb0 y vy tc0].
        { rewrite (tree_rep_spec E). normalize. }
      forward_call (ta0, x, vx, tb0, y, vy, tc0, b0, p0, pa, pbc). (* turn_left(t, p, q); *)
      Intros pc.
      forward. (* t = &q->left; *) simpl in H.
      Exists (field_address t_struct_tree [StructField _left] pbc) ta0 x vx tb0 (fun t => P (T t y vy tc0)).
      entailer!.
      unfold_data_at 2%nat.
      rewrite (treebox_rep_tree_rep (T _ _ _ _)). Exists p0. rewrite (field_at_data_at _ _ [StructField _left]); cancel.
      eapply derives_trans; [| apply (partial_treebox_rep_partial_treebox_rep _ _ _ b0)].
      cancel.
      eapply derives_trans; [| apply partial_treebox_rep_singleton_left; auto].
      cancel.
      rewrite treebox_rep_tree_rep. Exists pc. rewrite field_at_data_at; cancel.
Qed.

Definition delete_inv (b0: val) (t0: tree val) (x: nat): environ -> mpred :=
  EX b: val, EX t: tree val, EX P: tree val -> tree val,
  PROP(P (delete x t) = delete x t0)
  LOCAL(temp _t b; temp _x (Vint (Int.repr (Z.of_nat x))))
  SEP(treebox_rep t b; partial_treebox_rep P b0 b).

Lemma body_delete: semax_body Vprog Gprog f_delete delete_spec.
Proof.
  start_function.
  forward_loop (delete_inv b t x).
  * (* Precondition *)
    unfold delete_inv.
    Exists b t (fun t: tree val => t). entailer!.
    apply emp_partial_treebox_rep_H.
  * (* Loop body *)
    unfold delete_inv.
    Intros b1 t1 P.
    rewrite treebox_rep_tree_rep. Intros p1.
    forward. (* p = *t; *)
    forward_if.
    + (* then clause *)
      subst p1.
      assert_PROP (t1= (@E _)).
        1: entailer!.
      subst t1. rewrite (tree_rep_spec E). rewrite !prop_true_andp by auto.
      forward. (* return; *)
      rewrite <- H0.
      eapply derives_trans; [| apply (treebox_rep_partial_treebox_rep _ _ b1); auto].
      cancel.
      rewrite treebox_rep_spec; Exists nullval; simpl.
      entailer!.
    + (* else clause *)
      destruct t1.
        { rewrite (tree_rep_spec E). normalize. }
      rewrite tree_rep_treebox_rep; Intros.
      clear H1.
      forward. (* y=p->key; *)
      forward_if; [ | forward_if ].
      - (* Inner if, then clause: x<k *)
        forward. (* t=&p->left *)
        unfold delete_inv.
        Exists (field_address t_struct_tree [StructField _left] p1) t1_1 (fun t => P (T t k v t1_2)).
        entailer!.
       ** rewrite <- H0.
          simpl; simpl_compb; auto.
       ** sep_apply (partial_treebox_rep_singleton_left t1_2 k v p1 b1); auto.
          apply partial_treebox_rep_partial_treebox_rep.
      - (* Inner if, second branch:  k<x *)
        forward. (* t=&p->right *)
        unfold delete_inv.
        Exists (field_address t_struct_tree [StructField _right] p1) t1_2 (fun t => P (T t1_1 k v t)).
        entailer!.
       ** rewrite <- H0.
          simpl; simpl_compb; simpl_compb; auto.
       ** sep_apply (partial_treebox_rep_singleton_right t1_1 k v p1 b1); auto.
          apply partial_treebox_rep_partial_treebox_rep.
      - (* Inner if, third branch: x=k *)
        assert (x=k) by omega.
        subst x.
        forward_call (t1_1, k, v, t1_2, b1, p1).
        forward. (* return *)
        rewrite <- H0.
        simpl; simpl_compb; simpl_compb.
        apply treebox_rep_partial_treebox_rep.
Qed.
