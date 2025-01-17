Require Import VST.veric.base.
Require Import VST.veric.shares.
Require Import VST.shared.share_alg.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.res_predicates.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.zlist.sublist.

Definition cleave (sh: share) :=
  (Share.lub (fst (Share.split (Share.glb Share.Lsh sh))) (fst (Share.split (Share.glb Share.Rsh sh))),
   Share.lub (snd (Share.split (Share.glb Share.Lsh sh))) (snd (Share.split (Share.glb Share.Rsh sh)))).

Lemma cleave_join:
 forall sh: share, sepalg.join (fst (cleave sh)) (snd (cleave sh)) sh.
Proof.
intros.
unfold cleave.
destruct (Share.split (Share.glb Share.Lsh sh)) as [a b] eqn:?H.
apply split_join in H.
destruct (Share.split (Share.glb Share.Rsh sh)) as [e f] eqn:?H.
apply split_join in H0.
destruct (Share.split sh) as [c g] eqn:?H.
apply split_join in H1.
simpl.
destruct H1.
subst sh.
destruct H.
destruct H0.
split.
*
rewrite !Share.distrib1.
rewrite !(Share.glb_commute (Share.lub _ _)).
rewrite !Share.distrib1.
rewrite (Share.glb_commute b a) (Share.glb_commute f e).
rewrite H H0.
rewrite (Share.lub_commute Share.bot).
rewrite !Share.lub_bot.
rewrite Share.distrib2.
rewrite !(Share.lub_commute (Share.glb _ _)).
rewrite !Share.distrib2.
rewrite (Share.lub_commute f e) H3 H2.
rewrite (Share.glb_commute (Share.lub _ _)).
rewrite (Share.glb_assoc Share.Lsh).
rewrite !(Share.glb_assoc Share.Rsh).
rewrite (Share.glb_commute _ (Share.glb Share.Lsh _)).
rewrite (Share.glb_assoc Share.Lsh).
rewrite <- (Share.glb_assoc Share.Rsh).
rewrite (Share.glb_commute Share.Rsh).
rewrite glb_Lsh_Rsh.
rewrite Share.glb_commute. apply Share.glb_bot.
*
rewrite Share.lub_assoc.
rewrite (Share.lub_commute e).
rewrite (Share.lub_assoc b).
rewrite <- Share.lub_assoc.
rewrite H2.
rewrite (Share.lub_commute f e) H3.
clear.
do 2 rewrite (Share.glb_commute _ (Share.lub _ _)).
rewrite <- Share.distrib1.
rewrite lub_Lsh_Rsh.
apply Share.glb_top.
Qed.

Lemma cleave_readable1:
 forall sh, readable_share sh -> readable_share (fst (cleave sh)).
Proof.
intros.
hnf in H|-*. contradict H.
apply identity_share_bot in H.
unfold cleave in H.
simpl in H.
rewrite Share.distrib1 in H.
apply lub_bot_e in H. destruct H as [_ ?].
destruct (Share.split (Share.glb Share.Rsh sh)) as [c d] eqn:H1.
apply (split_nontrivial' _ _ _ H1).
left.
apply split_join in H1.
simpl in *.
destruct (join_parts1 comp_Rsh_Lsh H1).
rewrite <- H0, H.
apply bot_identity.
Qed.

Lemma cleave_readable2:
 forall sh, readable_share sh -> readable_share (snd (cleave sh)).
Proof.
intros.
hnf in H|-*. contradict H.
apply identity_share_bot in H.
unfold cleave in H.
simpl in H.
rewrite Share.distrib1 in H.
apply lub_bot_e in H. destruct H as [_ ?].
destruct (Share.split (Share.glb Share.Rsh sh)) as [c d] eqn:H1.
apply (split_nontrivial' _ _ _ H1).
simpl in *.
right.
apply split_join in H1.
apply sepalg.join_comm in H1.
simpl in *.
destruct (join_parts1 comp_Rsh_Lsh H1).
rewrite <- H0, H.
apply bot_identity.
Qed.


Section heap.
Context `{!gen_heapGS share address resource Σ} `{!wsatGS Σ}.

Lemma share_join_op: forall (sh1 sh2 sh : share), sepalg.join sh1 sh2 sh ->
  Share sh1 ⋅ Share sh2 = Share sh.
Proof.
  intros *; rewrite -share_op_is_join.
  intros; rewrite share_op_equiv; eauto.
Qed.

Lemma mapsto_share_join: forall sh1 sh2 sh l r, sepalg.join sh1 sh2 sh ->
  readable_share sh1 -> readable_share sh2 ->
  l ↦{#sh1} r ∗ l ↦{#sh2} r ⊣⊢ l ↦{#sh} r.
Proof.
  intros; rewrite -mapsto_split; try done.
  rewrite dfrac_op_own.
  erewrite share_join_op; try done; intros ->; contradiction bot_unreadable.
Qed.

Lemma address_mapsto_share_join:
 forall (sh1 sh2 sh : share) ch v a,
   sepalg.join sh1 sh2 sh ->
   readable_share sh1 -> readable_share sh2 ->
   address_mapsto ch v sh1 a ∗ address_mapsto ch v sh2 a
    ⊣⊢ address_mapsto ch v sh a.
Proof.
  intros.
  rewrite /address_mapsto.
  setoid_rewrite big_sepL_proper at 3; last by intros; symmetry; apply mapsto_share_join.
  setoid_rewrite big_sepL_sep.
  iSplit.
  - iIntros "[H1 H2]".
    iDestruct "H1" as (bl1 (? & ? & ?)) "H1".
    iDestruct "H2" as (bl (? & ? & ?)) "H2".
    iDestruct (mapsto_list_value_cohere with "[$H1 $H2]") as %->.
    { congruence. }
    iExists bl; iSplit; first auto.
    iSplitL "H1"; done.
  - iIntros "H".
    iDestruct "H" as (bl ?) "H".
    rewrite bi.sep_exist_r; iExists bl.
    rewrite bi.sep_exist_l; iExists bl.
    by iFrame "%".
Qed.

Lemma address_mapsto_share_joins:
 forall (sh1 sh2 : share) ch v a,
   address_mapsto ch v sh1 a ∗ address_mapsto ch v sh2 a ⊢ ⌜sepalg.joins sh1 sh2⌝.
Proof.
  intros.
  rewrite /address_mapsto.
  iIntros "((%bl1 & (% & %) & H1) & (%bl2 & % & H2))".
  destruct (size_chunk_nat_pos ch) as (? & ?).
  destruct bl1, bl2; simpl in *; try lia.
  iDestruct "H1" as "(H1 & _)"; iDestruct "H2" as "(H2 & _)".
  iDestruct (mapsto_valid_2 with "H1 H2") as %(Hsh & _); iPureIntro.
  apply share_valid2_joins in Hsh as (? & ? & ? & [=] & [=] & ? & Hsh); subst.
  rewrite share_op_is_join in Hsh; eexists; eauto.
Qed.

Lemma mapsto_no_mapsto_share_join: forall sh1 sh2 sh l r (nsh : ~readable_share sh1), sepalg.join sh1 sh2 sh ->
  readable_share sh2 ->
  mapsto_no l sh1 ∗ l ↦{#sh2} r ⊣⊢ l ↦{#sh} r.
Proof.
  intros; rewrite -mapsto_split_no; try done.
  rewrite dfrac_op_own.
  erewrite share_join_op; try done; intros ->; contradiction bot_unreadable.
Qed.

Lemma mapsto_mapsto_no_share_join: forall sh1 sh2 sh l r (nsh : ~readable_share sh2), sepalg.join sh1 sh2 sh ->
  readable_share sh1 ->
  l ↦{#sh1} r ∗ mapsto_no l sh2 ⊣⊢ l ↦{#sh} r.
Proof.
  intros; rewrite -(mapsto_no_mapsto_share_join _ _ sh); [| | apply sepalg.join_comm, H | ..]; try done.
  by rewrite comm.
Qed.

Lemma mapsto_no_share_join: forall sh1 sh2 sh l (nsh1 : ~readable_share sh1) (nsh2 : ~readable_share sh2), sepalg.join sh1 sh2 sh ->
  mapsto_no l sh1 ∗ mapsto_no l sh2 ⊣⊢ mapsto_no l sh.
Proof.
  intros; rewrite -mapsto_no_split // share_op_is_join //.
Qed.

Lemma nonlock_permission_bytes_address_mapsto_join:
 forall (sh1 sh2 sh : share) ch v a,
   sepalg.join sh1 sh2 sh ->
   readable_share sh2 ->
   nonlock_permission_bytes sh1 a (Memdata.size_chunk ch)
     ∗ address_mapsto ch v sh2 a
    ⊣⊢ address_mapsto ch v sh a.
Proof.
  intros.
  rewrite /nonlock_permission_bytes /address_mapsto.
  rewrite bi.sep_exist_l.
  apply bi.exist_proper; intros bl.
  rewrite !(big_sepL_seq bl).
  iSplit.
  - iIntros "[H1 [%Hbl H2]]"; iFrame "%".
    destruct Hbl as [-> _].
    rewrite /size_chunk_nat.
    iPoseProof (big_sepL_sep_2 with "H1 H2") as "H".
    iApply (big_sepL_mono with "H").
    intros; iIntros "[H1 H2]".
    destruct (readable_share_dec _).
    + iDestruct "H1" as (??) "H1".
      iDestruct (mapsto_combine with "H1 H2") as "[? ->]".
      rewrite dfrac_op_own; erewrite share_join_op; done.
    + iDestruct (mapsto_no_mapsto_combine with "H1 H2") as "?".
      rewrite dfrac_op_own; erewrite share_join_op; done.
  - iIntros "[%Hbl H]"; iFrame "%".
    destruct Hbl as [-> _].
    rewrite /size_chunk_nat.
    rewrite -big_sepL_sep.
    iApply (big_sepL_mono with "H").
    intros; iIntros "H".
    destruct (readable_share_dec _).
    + rewrite -mapsto_share_join; try done.
      iDestruct "H" as "[? $]".
      iExists _; iSplit; last done; done.
    + rewrite -mapsto_no_mapsto_share_join //.
Qed.

Lemma nonlock_permission_bytes_address_mapsto_joins:
 forall (sh1 sh2 : share) ch v a,
   nonlock_permission_bytes sh1 a (Memdata.size_chunk ch)
     ∗ address_mapsto ch v sh2 a
    ⊢ ⌜sepalg.joins sh1 sh2⌝.
Proof.
  intros.
  rewrite /nonlock_permission_bytes /address_mapsto.
  iIntros "(H1 & (%bl2 & (% & %) & H2))".
  destruct (size_chunk_nat_pos ch) as (? & Hch).
  destruct bl2; simpl in *; try lia.
  rewrite /size_chunk_nat in Hch; rewrite Hch -cons_seq /=.
  iDestruct "H1" as "(H1 & _)"; iDestruct "H2" as "(H2 & _)".
  if_tac.
  - iDestruct "H1" as (? _) "H1".
    iDestruct (mapsto_valid_2 with "H1 H2") as %(Hsh & _); iPureIntro.
    apply share_valid2_joins in Hsh as (? & ? & ? & [=] & [=] & ? & Hsh); subst.
    rewrite share_op_is_join in Hsh; eexists; eauto.
  - iDestruct (mapsto_no_mapsto_valid_2 with "H1 H2") as %(Hsh & _); iPureIntro.
    apply share_valid2_joins in Hsh as (? & ? & ? & [=] & [=] & ? & Hsh); subst.
    rewrite share_op_is_join in Hsh; eexists; eauto.
Qed.


Lemma VALspec_range_share_join:
 forall sh1 sh2 sh n p,
  readable_share sh1 ->
  readable_share sh2 ->
  sepalg.join sh1 sh2 sh ->
  VALspec_range n sh1 p ∗
  VALspec_range n sh2 p ⊣⊢
  VALspec_range n sh p.
Proof.
  intros.
  rewrite /VALspec_range /VALspec.
  rewrite -big_sepL_sep.
  apply big_sepL_proper; intros.
  iSplit.
  - iIntros "[H1 H2]"; iDestruct "H1" as (v1) "H1"; iDestruct "H2" as (v) "H2".
    iDestruct (mapsto_value_cohere with "[$H1 $H2]") as %->.
    iExists v; rewrite -(mapsto_share_join _ _ sh); try done; iFrame.
  - iIntros "H"; iDestruct "H" as (v) "H".
    rewrite bi.sep_exist_r; iExists v.
    rewrite bi.sep_exist_l; iExists v.
    by rewrite mapsto_share_join.
Qed.

Lemma nonlock_permission_bytes_share_join:
 forall sh1 sh2 sh a n,
  sepalg.join sh1 sh2 sh ->
  nonlock_permission_bytes sh1 a n ∗
  nonlock_permission_bytes sh2 a n ⊣⊢
  nonlock_permission_bytes sh a n.
Proof.
  intros.
  rewrite /nonlock_permission_bytes -big_sepL_sep.
  apply big_sepL_proper; intros.
  pose proof (readable_share_join H).
  repeat destruct (readable_share_dec _); try solve [match goal with H : ~readable_share sh |- _ => contradiction H; auto end];
    try solve [exfalso; eapply join_unreadable_shares; eauto].
  - rewrite bi.sep_exist_r; apply bi.exist_proper; intros ?.
    rewrite bi.sep_exist_l -(mapsto_share_join _ _ sh); try done.
    iSplit; [iIntros "(% & [(% & ?) (% & ?)])" | iIntros "(% & $ & ?)"].
    + iDestruct (mapsto_value_cohere with "[$]") as %->; by iFrame.
    + iExists _; by iFrame.
  - rewrite bi.sep_exist_r; apply bi.exist_proper; intros ?.
    rewrite -bi.persistent_and_sep_assoc; apply bi.and_proper; first done.
    by apply mapsto_mapsto_no_share_join.
  - rewrite bi.sep_exist_l; apply bi.exist_proper; intros ?.
    rewrite comm -bi.persistent_and_sep_assoc; apply bi.and_proper; first done.
    rewrite comm; by apply mapsto_no_mapsto_share_join.
  - by apply mapsto_no_share_join.
Qed.

Lemma nonlock_permission_bytes_share_joins:
 forall sh1 sh2 a n, (n > 0)%Z ->
  nonlock_permission_bytes sh1 a n ∗
  nonlock_permission_bytes sh2 a n ⊢
  ⌜sepalg.joins sh1 sh2⌝.
Proof.
  intros.
  rewrite /nonlock_permission_bytes.
  iIntros "(H1 & H2)".
  destruct (Z.to_nat n) eqn: Hn; first lia.
  rewrite -cons_seq /=.
  iDestruct "H1" as "(H1 & _)"; iDestruct "H2" as "(H2 & _)".
  if_tac.
  - iDestruct "H1" as (? _) "H1".
    if_tac.
    + iDestruct "H2" as (? _) "H2".
      iDestruct (mapsto_valid_2 with "H1 H2") as %(Hsh & _); iPureIntro.
      apply share_valid2_joins in Hsh as (? & ? & ? & [=] & [=] & ? & Hsh); subst.
      rewrite share_op_is_join in Hsh; eexists; eauto.
    + iDestruct (mapsto_no_mapsto_valid_2 with "H2 H1") as %(Hsh & _); iPureIntro.
      apply share_valid2_joins in Hsh as (? & ? & ? & [=] & [=] & ? & Hsh); subst.
      rewrite share_op_is_join in Hsh; eexists; apply sepalg.join_comm; eauto.
  - if_tac.
    + iDestruct "H2" as (? _) "H2".
      iDestruct (mapsto_no_mapsto_valid_2 with "H1 H2") as %(Hsh & _); iPureIntro.
      apply share_valid2_joins in Hsh as (? & ? & ? & [=] & [=] & ? & Hsh); subst.
      rewrite share_op_is_join in Hsh; eexists; eauto.
    + iDestruct (mapsto_no_valid_2 with "H1 H2") as %(Hsh & _); iPureIntro.
      apply share_valid2_joins in Hsh as (? & ? & ? & [=] & [=] & ? & Hsh); subst.
      rewrite share_op_is_join in Hsh; eexists; eauto.
Qed.

Lemma nonlock_permission_bytes_VALspec_range_join:
 forall sh1 sh2 sh p n,
  sepalg.join sh1 sh2 sh ->
  readable_share sh2 ->
  nonlock_permission_bytes sh1 p n ∗
  VALspec_range n sh2 p ⊣⊢
  VALspec_range n sh p.
Proof.
  intros.
  rewrite /nonlock_permission_bytes /VALspec_range.
  rewrite -big_sepL_sep.
  apply big_sepL_proper; intros.
  rewrite /VALspec bi.sep_exist_l; apply bi.exist_proper; intros v.
  if_tac.
  - rewrite -(mapsto_share_join _ _ sh) //.
    iSplit.
    + iIntros "[(% & % & H1) H2]".
      iDestruct (mapsto_value_cohere with "[$H1 $H2]") as %->; iFrame.
    + iIntros "[? $]".
      iExists _; iFrame.
  - rewrite mapsto_no_mapsto_share_join //.
Qed.

(*Lemma is_resource_pred_YES_LK lock_size (l: address) (R: pred rmap) sh:
  is_resource_pred
    (fun l' => yesat (SomeP rmaps.Mpred (fun _ => R)) (LK lock_size (snd l' - snd l)) sh l')
    (fun r (l': address) n => exists p, r = YES sh p (LK lock_size (snd l' - snd l))
        (SomeP rmaps.Mpred (fun _ => approx n R))).
Proof. hnf; intros. reflexivity. Qed.*)

(*Lemma LKspec_share_join lock_size:
 forall sh1 sh2 sh R p,
  sepalg.join sh1 sh2 sh ->
  readable_share sh1 -> readable_share sh2 ->
  LKspec lock_size R sh1 p ∗
  LKspec lock_size R sh2 p ⊣⊢
  LKspec lock_size R sh p.
Proof.
  intros.
  rewrite /LKspec -big_sepL_sep.
  apply big_sepL_proper; intros.
  rewrite assoc -(bi.sep_assoc (_ ↦{_} _)) (bi.sep_comm (inv _ _)) assoc mapsto_share_join //.
  rewrite -assoc -bi.persistent_sep_dup //.
Qed.*)

End heap.

(* It's often useful to split Tsh in half. *)
Definition gsh1 := fst (slice.cleave Tsh).
Definition gsh2 := snd (slice.cleave Tsh).

Lemma readable_gsh1 : readable_share gsh1.
Proof.
  apply slice.cleave_readable1; auto.
Qed.

Lemma readable_gsh2 : readable_share gsh2.
Proof.
  apply slice.cleave_readable2; auto.
Qed.

Lemma gsh1_gsh2_join : sepalg.join gsh1 gsh2 Tsh.
Proof.
  apply slice.cleave_join; unfold gsh1, gsh2; destruct (slice.cleave Tsh); auto.
Qed.

#[export] Hint Resolve readable_gsh1 readable_gsh2 gsh1_gsh2_join : core.

Lemma gsh1_not_bot : gsh1 <> Share.bot.
Proof.
  intro X; contradiction bot_unreadable; rewrite <- X; auto.
Qed.

Lemma gsh2_not_bot : gsh2 <> Share.bot.
Proof.
  intro X; contradiction bot_unreadable; rewrite <- X; auto.
Qed.
#[export] Hint Resolve gsh1_not_bot gsh2_not_bot : core.

Lemma split_readable_share sh :
  readable_share sh ->
  exists sh1, exists sh2,
    readable_share sh1 /\
    readable_share sh2 /\
    sepalg.join sh1 sh2 sh.
Proof.
  intros.
  pose proof (slice.cleave_readable1 _ H); pose proof (slice.cleave_readable2 _ H).
  destruct (slice.cleave sh) as (sh1, sh2) eqn: Hsplit.
  exists sh1, sh2; split; [|split]; auto.
  replace sh1 with (fst (slice.cleave sh)) by (rewrite Hsplit; auto).
  replace sh2 with (snd (slice.cleave sh)) by (rewrite Hsplit; auto).
  apply slice.cleave_join; auto.
Qed.

Lemma split_Ews :
  exists sh1, exists sh2,
    readable_share sh1 /\
    readable_share sh2 /\
    sepalg.join sh1 sh2 Ews.
Proof.
  apply split_readable_share; auto.
Qed.

(* Split a share into an arbitrary number of subshares. *)
Lemma split_shares : forall n sh, readable_share sh ->
  exists sh1 shs, Zlength shs = Z.of_nat n /\ readable_share sh1 /\ Forall readable_share shs /\
                  sepalg_list.list_join sh1 shs sh.
Proof.
  induction n; intros.
  - exists sh, nil; repeat split; auto.
    apply sepalg_list.fold_rel_nil.
  - destruct (split_readable_share _ H) as (sh1 & sh2 & H1 & ? & ?).
    destruct (IHn _ H1) as (sh1' & shs & ? & ? & ? & ?).
    exists sh1', (shs ++ sh2 :: nil).
    rewrite -> Nat2Z.inj_succ, Zlength_app, Zlength_cons, Zlength_nil; split; [lia|].
    rewrite Forall_app; repeat split; auto.
    eapply sepalg_list.list_join_app; eauto.
    rewrite <- sepalg_list.list_join_1; auto.
Qed.
