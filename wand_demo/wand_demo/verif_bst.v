Require Import VST.floyd.proofauto.
Require Import VFA.Maps.
Require Import VFA.SearchTree.
Require Import WandDemo.SearchTree_ext.
Require Import WandDemo.bst.
Require Import WandDemo.bst_lemmas.
Require Import WandDemo.VST_lemmas.
Require Import WandDemo.spec_bst.

(***************************************************************)
(*                                                             *)
(* This file contains the formal verification of BST insert    *)
(* and the alternative proofs using traditional definitions of *)
(* partial tree predicates. Those proofs and tactics outside   *)
(* Modules are shared.                                         *)
(*                                                             *)
(* Magic-wand-as-frame proof is in                             *)
(*  Module insert_by_WandQFrame_Func_Hole.                     *)
(*                                                             *)
(* Quantifier free version of Magic-wand-as-frame proof is in  *)
(*  Module insert_by_WandFrame.                                *)
(*                                                             *)
(* Another version of Magic-wand-as-frame proof is in          *)
(*  Module insert_by_WandQFrame_Ind_Hole.                      *)
(*                                                             *)
(* The proof using traditionally defined partial_treebox_rep   *)
(* is in                                                       *)
(*  Module insert_by_Ind_Pred_Ind_Hole.                        *)
(*                                                             *)
(*                                                             *)
(***************************************************************)

Lemma if_trueb: forall {A: Type} b (a1 a2: A), b = true -> (if b then a1 else a2) = a1.
Proof. intros; subst; auto. Qed.

Lemma if_falseb: forall {A: Type} b (a1 a2: A), b = false -> (if b then a1 else a2) = a2.
Proof. intros; subst; auto. Qed.

Ltac simpl_compb := first [ rewrite if_trueb by (apply NPeano.Nat.ltb_lt; rewrite Nat2Z.inj_lt; omega)
                          | rewrite if_falseb by (apply NPeano.Nat.ltb_nlt; rewrite Nat2Z.inj_lt; omega)].

Lemma insert_concrete_to_abstract:
 forall {Espec: OracleKind} CMD p0 x v m0,
 (forall t0, 
   semax (func_tycontext f_insert Vprog Gprog [])
    (PROP ( )
     LOCAL (temp _p p0; temp _x (Vint (Int.repr (Z.of_nat x))); temp _value v)  
     SEP (treebox_rep t0 p0)) CMD
   (frame_ret_assert
     (function_body_ret_assert tvoid
        (PROP ( )  LOCAL ()  SEP (treebox_rep (insert x v t0) p0))) emp))  ->
 semax (func_tycontext f_insert Vprog Gprog [])
   (PROP ( )
    LOCAL (temp _p p0; temp _x (Vint (Int.repr (Z.of_nat x))); temp _value v)
    SEP (Mapbox_rep m0 p0)) CMD
  (frame_ret_assert
    (function_body_ret_assert tvoid
     (PROP ( )  LOCAL ()  SEP (Mapbox_rep (t_update m0 x v) p0))) emp).
Proof.
  intros.
  rewrite !Mapbox_rep_unfold.
  Intros t0.
  apply (semax_post'' (PROP () LOCAL () SEP (treebox_rep (insert x v t0) p0))); auto.
  Exists (insert x v t0).
  entailer!.
  split; [apply insert_relate | apply insert_SearchTree]; auto.
Qed.

Module insert_by_WandQFrame_Func_Hole.

Import PartialTreeboxRep_WandQFrame_Func_Hole.

Lemma body_insert: semax_body Vprog Gprog f_insert insert_spec.
Proof.
  start_function.
  apply insert_concrete_to_abstract; intros.
  abbreviate_semax.
  forward_loop (EX p: val, EX t: tree val, EX P: tree val -> tree val,
       PROP(P (insert x v t) = (insert x v t0))
       LOCAL(temp _p p; temp _x (Vint (Int.repr (Z.of_nat x)));   temp _value v)
       SEP(treebox_rep t p;  partial_treebox_rep P p0 p)).
  * (* Precondition *)
    Exists p0 t0 (fun t: tree val => t). entailer!.
    apply emp_partial_treebox_rep_H.
  * (* Loop body *)
    Intros p t P.
    rewrite treebox_rep_tree_rep at 1. Intros q.
    forward. (* q = * p; *)
    forward_if.
    + (* then clause *)
      subst q.
      forward_call (sizeof t_struct_tree).
        1: simpl; rep_omega.
      Intros q.
      rewrite memory_block_data_at_ by auto.
      forward. (* q->key=x; *)
      forward. (* q->value=value; *)
      forward. (* q->left=NULL; *)
      forward. (* q->right=NULL; *)
      assert_PROP (t = (@E _)) by entailer!.
      subst t. rewrite tree_rep_treebox_rep. normalize.
      forward. (* * p = q; *)
      forward. (* return; *)
      entailer!.  clear - H1 H0 H.
      sep_apply (treebox_rep_leaf x q p v); auto.
      rewrite <- H1. apply treebox_rep_partial_treebox_rep.
    + (* else clause *)
      destruct t; rewrite tree_rep_treebox_rep.
      { normalize. }
      Intros. clear H2.
      forward. (* y=q->key; *)
      forward_if; [ | forward_if ].
      - (* Inner if, then clause: x<k *)
        forward. (* p=&q->left *)
        Exists (field_address t_struct_tree [StructField _left] q) t1 (fun t1 => P (T t1 k v0 t2)).
        entailer!.
       ** rewrite <- H1.
          simpl; simpl_compb; auto.
       ** sep_apply (partial_treebox_rep_singleton_left t2 k v0 q p); auto.
          apply partial_treebox_rep_partial_treebox_rep.
      - (* Inner if, second branch:  k<x *)
        forward. (* p=&q->right *)
        Exists (field_address t_struct_tree [StructField _right] q) t2 (fun t2 => P (T t1 k v0 t2)).
        entailer!.
       ** rewrite <- H1.
          simpl; simpl_compb; simpl_compb; auto.
       ** sep_apply (partial_treebox_rep_singleton_right t1 k v0 q p); auto.
          cancel; apply partial_treebox_rep_partial_treebox_rep.
      - (* Inner if, third branch: x=k *)
        assert (x=k) by omega.
        subst x. clear H H2 H5.
        forward. (* q->value=value *)
        forward. (* return *)
        entailer!.
        rewrite <- H1.
        simpl insert. simpl_compb; simpl_compb.
        sep_apply (treebox_rep_internal t1 k v t2 p q); auto.
        apply treebox_rep_partial_treebox_rep.
Qed.

End insert_by_WandQFrame_Func_Hole.

Module insert_by_WandFrame.

Import PartialTreeboxRep_WandFrame.

Lemma body_insert: semax_body Vprog Gprog f_insert insert_spec.
Proof.
  start_function.
  apply insert_concrete_to_abstract; intros.
  abbreviate_semax.
  forward_loop (EX p: val, EX t: tree val,
      PROP()
      LOCAL(temp _p p; temp _x (Vint (Int.repr (Z.of_nat x)));   temp _value v)
      SEP(treebox_rep t p;  (treebox_rep (insert x v t) p -* treebox_rep (insert x v t0) p0))).
  * (* Precondition *)
    Exists p0 t0. entailer.
    apply ramify_PPQQ.
  * (* Loop body *)
    Intros p t.
    rewrite treebox_rep_tree_rep at 1. Intros q.
    forward. (* q = * p; *)
    forward_if.
    + (* then clause *)
      subst q.
      forward_call (sizeof t_struct_tree).
        1: simpl; rep_omega.
      Intros q.
      rewrite memory_block_data_at_ by auto.
      forward. (* q->key=x; *)
      simpl.
      forward. (* q->value=value; *)
      forward. (* q->left=NULL; *)
      forward. (* q->right=NULL; *)
      assert_PROP (t = (@E _)).
        1: entailer!.
      subst t. rewrite tree_rep_treebox_rep. rewrite !prop_true_andp by auto.
      forward. (* * p = q; *)
      forward. (* return; *)
      entailer!.
      sep_apply (treebox_rep_leaf x q p v); auto.
      apply treebox_rep_partial_treebox_rep.
    + (* else clause *)
      destruct t; rewrite tree_rep_treebox_rep.
      { normalize. }
      Intros. clear H1. simpl in H3.
      forward. (* y=q->key; *)
      forward_if; [ | forward_if ].
      - (* Inner if, then clause: x<k *)
        forward. (* p=&q->left *)
        Exists (field_address t_struct_tree [StructField _left] q) t1.
        entailer!.
        simpl treebox_rep.
        simpl_compb.
        sep_apply (partial_treebox_rep_singleton_left (insert x v t1) t2 k v0 q p); auto.
        cancel; apply partial_treebox_rep_partial_treebox_rep.
      - (* Inner if, second branch:  k<x *)
        forward. (* p=&q->right *)
        Exists (field_address t_struct_tree [StructField _right] q) t2.
        entailer!.
        simpl treebox_rep.
        simpl_compb; simpl_compb.
        sep_apply (partial_treebox_rep_singleton_right t1 (insert x v t2) k v0 q p); auto.
        cancel; apply partial_treebox_rep_partial_treebox_rep.
      - (* Inner if, third branch: x=k *)
        assert (x=k) by omega.
        subst x. clear H H1 H4.
        forward. (* q->value=value *)
        forward. (* return *)
        entailer!.
        simpl treebox_rep.
        simpl_compb; simpl_compb.
        sep_apply (treebox_rep_internal t1 k v t2 p q); auto.
        apply treebox_rep_partial_treebox_rep.
Qed.

End insert_by_WandFrame.

Module insert_by_WandQFrame_Ind_Hole.

Import PartialTreeboxRep_WandQFrame_Ind_Hole.

Lemma body_insert: semax_body Vprog Gprog f_insert insert_spec.
Proof.
  start_function.
  apply insert_concrete_to_abstract; intros.
  abbreviate_semax.
  forward_loop (EX p: val, EX t: tree val, EX pt: partial_tree val,
      PROP(partial_tree_tree pt (insert x v t) = (insert x v t0))
      LOCAL(temp _p p; temp _x (Vint (Int.repr (Z.of_nat x)));   temp _value v)
      SEP(treebox_rep t p;  partial_treebox_rep pt p0 p)).
  * (* Precondition *)
    Exists p0 t0 (@SearchTree_ext.H val). entailer!.
    apply emp_partial_treebox_rep_H.
  * (* Loop body *)
    Intros p t pt.
    rewrite treebox_rep_tree_rep at 1. Intros q.
    forward. (* q = * p; *)
    forward_if.
    + (* then clause *)
      subst q.
      forward_call (sizeof t_struct_tree).
        1: simpl; rep_omega.
      Intros q.
      rewrite memory_block_data_at_ by auto.
      forward. (* q->key=x; *)
      simpl.
      forward. (* q->value=value; *)
      forward. (* q->left=NULL; *)
      forward. (* q->right=NULL; *)
      assert_PROP (t = (@E _)).
        1: entailer!.
      subst t. rewrite tree_rep_treebox_rep. rewrite !prop_true_andp by auto.
      forward. (* * p = q; *)
      forward. (* return; *)
      entailer!.
      sep_apply (treebox_rep_leaf x q p v); auto.
      rewrite <- H1. apply treebox_rep_partial_treebox_rep.
    + (* else clause *)
      destruct t; rewrite tree_rep_treebox_rep.
      { normalize. }
      Intros. clear H2.
      forward. (* y=q->key; *)
      forward_if; [ | forward_if ].
      - (* Inner if, then clause: x<k *)
        forward. (* p=&q->left *)
        Exists (field_address t_struct_tree [StructField _left] q) t1 (partial_tree_partial_tree pt (SearchTree_ext.L SearchTree_ext.H k v0 t2)).
        entailer!.
       ** rewrite partial_tree_partial_tree_tree.
          rewrite <- H1.
          simpl; simpl_compb; auto.
       ** sep_apply (partial_treebox_rep_singleton_left t2 k v0 q p); auto.
          apply partial_treebox_rep_partial_treebox_rep.
      - (* Inner if, second branch:  k<x *)
        forward. (* p=&q->right *)
        Exists (field_address t_struct_tree [StructField _right] q) t2 (partial_tree_partial_tree pt (SearchTree_ext.R t1 k v0 SearchTree_ext.H)).
        entailer!.
       ** rewrite partial_tree_partial_tree_tree.
          rewrite <- H1.
          simpl; simpl_compb; simpl_compb; auto.
       ** sep_apply (partial_treebox_rep_singleton_right t1 k v0 q p); auto.
          cancel; apply partial_treebox_rep_partial_treebox_rep.
      - (* Inner if, third branch: x=k *)
        assert (x=k) by omega.
        subst x. clear H H2 H5.
        forward. (* q->value=value *)
        forward. (* return *)
        entailer!.
        rewrite <- H1.
        simpl insert.
        simpl_compb; simpl_compb.
        sep_apply (treebox_rep_internal t1 k v t2 p q); auto.
        apply treebox_rep_partial_treebox_rep.
Qed.

End insert_by_WandQFrame_Ind_Hole.

Module insert_by_Ind_Pred_Ind_Hole.

Import PartialTreeboxRep_Ind_Pred_Ind_Hole.

Opaque partial_treebox_rep.
Arguments partial_treebox_rep: simpl never.

Lemma body_insert: semax_body Vprog Gprog f_insert insert_spec.
Proof.
  start_function.
  apply insert_concrete_to_abstract; intros.
  abbreviate_semax.
  forward_loop (EX p: val, EX t: tree val, EX pt: partial_tree val,
      PROP(partial_tree_tree pt (insert x v t) = (insert x v t0))
      LOCAL(temp _p p; temp _x (Vint (Int.repr (Z.of_nat x)));   temp _value v)
      SEP(treebox_rep t p; partial_treebox_rep pt p0 p)).
  * (* Precondition *)
    Exists p0 t0 (@SearchTree_ext.H val). entailer!.
    apply emp_partial_treebox_rep_H.
  * (* Loop body *)
    Intros p t pt.
    rewrite treebox_rep_tree_rep at 1. Intros q.
    forward. (* q = * p; *)
    forward_if.
    + (* then clause *)
      subst q.
      forward_call (sizeof t_struct_tree).
        1: simpl; rep_omega.
      Intros q.
      rewrite memory_block_data_at_ by auto.
      forward. (* q->key=x; *)
      simpl.
      forward. (* q->value=value; *)
      forward. (* q->left=NULL; *)
      forward. (* q->right=NULL; *)
      assert_PROP (t = (@E _)).
        1: entailer!.
      subst t. rewrite tree_rep_treebox_rep. rewrite !prop_true_andp by auto.
      forward. (* * p = q; *)
      forward. (* return; *)
      entailer!.
      sep_apply (treebox_rep_leaf x q p v); auto.
      rewrite <- H1. apply treebox_rep_partial_treebox_rep.
    + (* else clause *)
      destruct t; rewrite tree_rep_treebox_rep.
      { normalize. }
      Intros. clear H2.
      forward. (* y=q->key; *)
      forward_if; [ | forward_if ].
      - (* Inner if, then clause: x<k *)
        forward. (* p=&q->left *)
        Exists (field_address t_struct_tree [StructField _left] q) t1 (partial_tree_partial_tree pt (SearchTree_ext.L SearchTree_ext.H k v0 t2)).
        entailer!.
       ** rewrite partial_tree_partial_tree_tree.
          rewrite <- H1.
          simpl; simpl_compb; auto.
       ** sep_apply (partial_treebox_rep_singleton_left t2 k v0 q p); auto.
          apply partial_treebox_rep_partial_treebox_rep.
      - (* Inner if, second branch:  k<x *)
        forward. (* p=&q->right *)
        Exists (field_address t_struct_tree [StructField _right] q) t2 (partial_tree_partial_tree pt (SearchTree_ext.R t1 k v0 SearchTree_ext.H)).
        entailer!.
       ** rewrite partial_tree_partial_tree_tree.
          rewrite <- H1.
          simpl; simpl_compb; simpl_compb; auto.
       ** sep_apply (partial_treebox_rep_singleton_right t1 k v0 q p); auto.
          cancel; apply partial_treebox_rep_partial_treebox_rep.
      - (* Inner if, third branch: x=k *)
        assert (x=k) by omega.
        subst x. clear H H2 H5.
        forward. (* q->value=value *)
        forward. (* return *)
        entailer!.
        rewrite <- H1.
        simpl insert.
        simpl_compb; simpl_compb.
        sep_apply (treebox_rep_internal t1 k v t2 p q); auto.
        apply treebox_rep_partial_treebox_rep.
Qed.

End insert_by_Ind_Pred_Ind_Hole.

