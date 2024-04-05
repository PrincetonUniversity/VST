Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.efield_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.stronger.
Require Import VST.floyd.entailer.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.proj_reptype_lemmas.
Require Import VST.floyd.replace_refill_reptype_lemmas.
Require Import VST.floyd.loadstore_field_at.
Require Import VST.floyd.nested_loadstore.

Section mpred.

Context `{!VSTGS OK_ty Σ}.

Definition array_with_hole {cs: compspecs} sh (t: type) lo hi n (al': list (reptype t)) p :=
⌜field_compatible (tarray t n) nil p⌝ ∧
(∀ cl: list (reptype t),
(data_at sh (tarray t (hi-lo)) cl (field_address0 (tarray t n) (ArraySubsc lo :: nil) p)
-∗ data_at sh (tarray t n) (sublist 0 lo al' ++ cl ++ sublist hi n al') p)).

Lemma array_with_hole_local_facts {cs: compspecs}: forall sh t lo hi n (al': list (reptype t)) p,
array_with_hole sh t lo hi n al' p ⊢
⌜field_compatible (tarray t n) nil p⌝.
Proof.
intros.
unfold array_with_hole. entailer!.
Qed.

Lemma wand_slice_array:
forall {cs: compspecs} lo hi n sh t (al: list (reptype t)) p,
0 <= lo <= hi ->
hi <= n ->
Zlength al = n ->
data_at sh (tarray t n) al p ⊣⊢
⌜field_compatible (tarray t n) nil p⌝ ∧
data_at sh (tarray t (hi-lo)) (sublist lo hi al) (field_address0 (tarray t n) (ArraySubsc lo :: nil) p) ∗
array_with_hole sh t lo hi n al p.
Proof.
  intros until p.
  intros H H0 H1.
  unfold data_at, array_with_hole.
  assert (forall n, reptype (tarray t n) = list (reptype t)).
  {
    intros.
    rewrite reptype_eq.
    auto.
  }
  iSplit.
  + iIntros "H".
    iDestruct (field_at_local_facts with "H") as %(H7 & H8).
    rewrite -!prop_and_same_derives' //.
    erewrite field_at_Tarray by (try done; lia).
    rewrite (split3seg_array_at' _ _ _ 0 lo hi n); try lia. iDestruct "H" as "(? & ? & ?)".
    2: { rewrite H1; lia. }
    rewrite !Z.sub_0_r /data_at; iFrame.
    iIntros (v) "H".
    unfold data_at.
    iDestruct (field_at_local_facts with "H") as %(? & H4).
    rewrite value_fits_eq in H4; simpl in H4.
    destruct H4.
    rewrite -> Z.max_r in H4 by lia.
    change (@Zlength (reptype t) v = hi - lo) in H4.
    erewrite (field_at_Tarray _ (tarray t n)) by (try done; lia).
    erewrite (split3seg_array_at' _ _ _ 0 lo hi n); try lia.
    2:{ autorewrite with sublist. lia. }
    autorewrite with norm.
    unfold tarray; autorewrite with sublist.
    rewrite H4.
    replace (hi - lo - (hi - lo) + hi) with hi by lia.
    replace (n - lo - (hi - lo) + hi) with n by lia.
    rewrite /data_at; iFrame.
    autorewrite with sublist; iFrame.
  + iIntros "(% & ? & _ & H)".
    rewrite /data_at; iSpecialize ("H" with "[$]").
    autorewrite with sublist.
    auto.
Qed.

Section SingletonHole.

Definition array_with_singleton_hole {cs: compspecs} sh (t: type) i n (al': list (reptype t)) p :=
∀ v:reptype t,
 (data_at sh t v (field_address (tarray t n) (ArraySubsc i :: nil) p) -∗ data_at sh (tarray t n) (upd_Znth i al' v) p).

Lemma array_with_singleton_hole_intro {cs: compspecs} sh: forall t i n (al: list (reptype t)) p,
  0 <= i < n ->
  data_at sh (tarray t n) al p ⊢
    data_at sh t (Znth i al) (field_address (tarray t n) (ArraySubsc i :: nil) p) ∗
      array_with_singleton_hole sh t i n al p.
Proof.
  intros.
  unfold data_at, array_with_singleton_hole.
  assert (forall n, reptype (tarray t n) = list (reptype t)).
  {
    intros.
    rewrite reptype_eq.
    auto.
  }
  saturate_local.
  assert (Zlength al = n).
  {
    destruct H2 as [? _].
    rewrite -> Z.max_r in H2 by lia.
    rewrite <- H2.
    reflexivity.
  }
  clear H2.
  erewrite field_at_Tarray.
      2: constructor.
      2: reflexivity.
      2: lia.
      2: apply JMeq_refl.
  erewrite (split3seg_array_at _ _ _ 0 i (i+1) n); try lia.
      2: change (nested_field_type (tarray t n) (ArraySubsc 0 :: nil)) with t; lia.
  autorewrite with sublist.
  rewrite sublist_len_1.
      2: change (nested_field_type (tarray t n) (ArraySubsc 0 :: nil)) with t; lia.
  erewrite array_at_len_1.
      2: apply JMeq_refl.
  rewrite field_at_data_at.
  change ((nested_field_type (tarray t n) (ArraySubsc i :: nil))) with t.
  cancel.
  iIntros.
  unfold data_at at 2.
  erewrite field_at_Tarray.
      2: constructor.
      2: reflexivity.
      2: lia.
      2: apply JMeq_refl.
  erewrite (split3seg_array_at _ _ _ 0 i (i+1) n); try lia.
      2: autorewrite with sublist; change (nested_field_type (tarray t n) (ArraySubsc 0 :: nil)) with t; lia.
  autorewrite with sublist.
  rewrite sublist_len_1.
      2: autorewrite with sublist; change (nested_field_type (tarray t n) (ArraySubsc 0 :: nil)) with t; lia.
  erewrite array_at_len_1.
      2: apply JMeq_refl.
  rewrite field_at_data_at.
  change ((nested_field_type (tarray t n) (ArraySubsc i :: nil))) with t.
  rewrite upd_Znth_same.
      2: change (nested_field_type (tarray t n) (ArraySubsc 0 :: nil)) with t; lia.
  rewrite sublist_upd_Znth_l; try lia.
      2: change (nested_field_type (tarray t n) (ArraySubsc 0 :: nil)) with t; lia.
  rewrite sublist_upd_Znth_r; try lia.
      2: change (nested_field_type (tarray t n) (ArraySubsc 0 :: nil)) with t; lia.
  iFrame.
Qed.

Lemma array_with_singleton_hole_elim {cs: compspecs} sh: forall t i n (a: reptype t) (al: list (reptype t)) p,
  data_at sh t a (field_address (tarray t n) (ArraySubsc i :: nil) p) ∗
    array_with_singleton_hole sh t i n al p ⊢
      data_at sh (tarray t n) (upd_Znth i al a) p.
Proof.
  intros.
  iIntros "(? & H)"; iApply "H"; done.
Qed.

End SingletonHole.

Definition splice_into_list {A} (lo hi: Z) (source target : list A) : list A :=
   sublist 0 lo target
   ++ source 
   ++ sublist hi (Zlength target) target.

Section SegmentHole.

Definition array_with_segment_hole {cs: compspecs} sh (t: type) lo hi n (al': list (reptype t)) p :=
∀ v: list (reptype t),
 (data_at sh (tarray t (hi - lo)) v (field_address0 (tarray t n) (ArraySubsc lo :: nil) p) -∗ data_at sh (tarray t n) (splice_into_list lo hi v al') p).

Lemma array_with_segment_hole_intro {cs: compspecs} sh: forall t lo hi n (al: list (reptype t)) p,
  0 <= lo <= hi ->
  hi <= n ->
  data_at sh (tarray t n) al p ⊢
    data_at sh (tarray t (hi - lo)) (sublist lo hi al) (field_address0 (tarray t n) (ArraySubsc lo :: nil) p) ∗
      array_with_segment_hole sh t lo hi n al p.
Proof.
  intros.
  unfold data_at at 1, array_with_segment_hole.
  assert (forall n, reptype (tarray t n) = list (reptype t)).
  {
    intros.
    rewrite reptype_eq.
    auto.
  }
  saturate_local.
  assert (Zlength al = n).
  {
    destruct H3 as [? _].
    rewrite -> Z.max_r in H3 by lia.
    rewrite <- H3.
    reflexivity.
  }
  clear H3.
  erewrite field_at_Tarray.
      2: constructor.
      2: reflexivity.
      2: lia.
      2: apply JMeq_refl.
  erewrite (split3seg_array_at _ _ _ 0 lo hi n); try lia.
      2: change (nested_field_type (tarray t n) (ArraySubsc 0 :: nil)) with t; lia.
  autorewrite with sublist.
  change (tarray t (hi - lo)) with (nested_field_array_type (tarray t n) nil lo hi).
  erewrite <- array_at_data_at''' by first [reflexivity | lia].
  cancel.
  iIntros "(? & ?)" (?) "?".
  unfold data_at at 2.
  iAssert ⌜Zlength v = hi - lo⌝ as %?.
  {
    iStopProof; saturate_local.
    destruct H13.
    clear - H H13.
    apply bi.pure_intro.
    rewrite -> Z.max_r in H13 by lia.
    exact H13.
  }
  erewrite field_at_Tarray.
      2: constructor.
      2: reflexivity.
      2: lia.
      2: apply JMeq_refl.
  erewrite (split3seg_array_at _ _ _ 0 lo hi n); try lia.
      2: unfold splice_into_list; autorewrite with sublist; change (nested_field_type (tarray t n) (ArraySubsc 0 :: nil)) with t; lia.
  erewrite <- array_at_data_at''' by first [reflexivity | lia].
  unfold splice_into_list.
  autorewrite with sublist.
  replace (hi - lo - Zlength v + hi) with hi by lia.
  replace (n - lo - Zlength v + hi) with n by lia.
  iFrame.
  autorewrite with sublist.
  iFrame.
Qed.

Lemma array_with_segment_hole_elim {cs: compspecs} sh: forall t lo hi n (a: list (reptype t)) (al: list (reptype t)) p,
  data_at sh (tarray t (hi - lo)) a (field_address0 (tarray t n) (ArraySubsc lo :: nil) p) ∗
    array_with_segment_hole sh t lo hi n al p ⊢
      data_at sh (tarray t n) (splice_into_list lo hi a al) p.
Proof.
  intros.
  iIntros "(? & H)"; iApply "H"; done.
Qed.

End SegmentHole.

End mpred.

#[export] Hint Resolve array_with_hole_local_facts : saturate_local.
