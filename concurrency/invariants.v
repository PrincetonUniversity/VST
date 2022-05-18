Require Import stdpp.namespaces.
Require Export VST.veric.invariants.
Require Import VST.msl.ghost_seplog.
Require Import VST.msl.sepalg_generators.
Require Import VST.veric.compcert_rmaps.
Require Import VST.concurrency.conclib.
Require Export VST.concurrency.ghostsI.
Require Import VST.veric.bi.
Require Import VST.msl.sepalg.
Require Import List.

Lemma iter_sepcon_eq : forall A, @invariants.iter_sepcon A = @iter_sepcon mpred A _ _.
Proof.
  intros; extensionality f; extensionality l.
  induction l; auto; simpl.
  rewrite IHl; auto.
Qed.

(*Lemma nth_replace_nth : forall {A} n l a (d : A), (n < length l)%nat ->
  nth n (replace_nth n l a) d = a.
Proof.
  induction n; destruct l; auto; simpl; intros; try lia.
  apply IHn; lia.
Qed.

Lemma nth_replace_nth' : forall {A} n m l a (d : A), m <> n ->
  nth m (replace_nth n l a) d = nth m l d.
Proof.
  induction n; destruct l; auto; destruct m; auto; simpl; intros; try lia.
  apply IHn; lia.
Qed.*)

Section Invariants.

Definition inv (N : namespace) P := EX i : iname, !!(N = nroot .@ (Pos.of_nat (S i))) && invariant i P.

Global Instance agree_persistent g P : Persistent (agree g P : mpred).
Proof.
  apply core_persistent; auto.
Qed.

Global Instance inv_persistent N P : Persistent (inv N P).
Proof.
  apply _.
Qed.

Global Instance inv_affine N P : Affine (inv N P).
Proof.
  apply _.
Qed.

Lemma invariant_dup : forall N P, inv N P = (inv N P * inv N P)%logic.
Proof.
  intros; apply pred_ext; rewrite <- (bi.persistent_sep_dup (inv N P)); auto.
Qed.

Lemma wsat_alloc : forall P, wsat * |> P |-- (|==> wsat * EX N : _, inv N P)%I.
Proof.
  intros.
  eapply derives_trans; [unseal_derives; apply wsat_alloc|].
  unfold inv.
  match goal with |- context[(|==> ?P)%pred] => change (|==> P)%pred with (|==> (P : mpred))%I end.
  iIntros ">[$ I]".
  iDestruct "I" as (i) "I".
  iExists _, i; iFrame; eauto.
Qed.

Lemma agree_join : forall g P1 P2, agree g P1 * agree g P2 |-- (|> P1 -* |> P2) * agree g P1.
Proof.
  constructor; apply agree_join.
Qed.

Lemma agree_join2 : forall g P1 P2, agree g P1 * agree g P2 |-- (|> P1 -* |> P2) * agree g P2.
Proof.
  constructor; apply agree_join2.
Qed.

Existing Instance token_PCM.

Lemma wsat_open : forall i P,
  wsat * invariant i P * ghost_set g_en (Ensembles.Singleton i) |--
  (|==> wsat * |> P * ghost_list g_dis (list_singleton i (Some tt)))%I.
Proof.
  intros; unfold wsat, invariant.
  iIntros "((H & inv1) & en1)". iDestruct "H" as (l lg lb) "((((% & inv) & dis) & en) & I)". iDestruct "inv1" as (g) "[snap agree]".
  iAssert (!! (i < length lg /\ Znth (Z.of_nat i) lg = g /\
    exists b, Znth (Z.of_nat i) lb = Some b)%nat) as %Hi.
  { iCombine "snap" "inv" as "inv"; unfold master_list; erewrite snap_master_join1.
    iDestruct "inv" as "[% inv]".
    apply list_incl_singleton in H0.
    destruct (lt_dec i (length lg));
      [|erewrite nth_overflow in H0 by (erewrite map_length, upto_length; lia); discriminate].
    erewrite nth_map' with (d' := 0) in H0 by (rewrite upto_length; lia).
    erewrite nth_upto in H0 by lia.
    destruct (Znth (Z.of_nat i) lb); inv H0; iPureIntro; eauto. }
  iDestruct "snap" as "_".
  iModIntro.
  destruct Hi as (? & ? & b & Hi).
  assert (nth i lb None = Some b) as Hi' by (rewrite <- nth_Znth' in Hi; auto).
  destruct b.
  erewrite ghost_list_nth with (n := i) by (erewrite nth_map' with (d' := None), Hi'; eauto; lia).
  iDestruct "dis" as "[token dis]".
  rewrite -> @iter_sepcon_eq, @iter_sepcon_Znth with (d := _)(i := Z.of_nat i)
    by (rewrite Zlength_upto; split; [|apply Nat2Z.inj_lt]; lia).
  erewrite Znth_upto, Hi by lia.
  iDestruct "I" as "((agree' & HP) & I)".
  subst; iDestruct (agree_join with "[agree agree']") as "[imp agree]"; first iFrame.
  iSplitR "token"; last iFrame.
  iSplitR "HP imp"; last (iApply "imp"; iFrame).
  iExists l, lg, (replace_nth i lb (Some false)).
  rewrite replace_nth_length predicates_hered.prop_true_andp; last auto.
  iSplitR "I agree".
  iSplitR "en en1".
  iSplitR "dis".
  - erewrite map_ext; [iFrame|].
    intros; simpl.
    destruct (eq_dec a (Z.of_nat i)); [subst; rewrite Znth_replace_nth | rewrite Znth_replace_nth'];
      auto; try lia.
    rewrite Hi; auto.
  - rewrite map_replace_nth; iFrame.
  - iCombine "en en1" as "en"; erewrite ghost_set_join.
    iDestruct "en" as "[% en]".
    erewrite Ensembles.Extensionality_Ensembles at 1; [iFrame | constructor; intros ? X].
    + destruct (eq_dec x i).
      * subst; unfold Ensembles.In; apply nth_replace_nth; lia.
      * inv X; unfold Ensembles.In in *.
        rewrite nth_replace_nth'; auto.
        { inv H2; contradiction. }
    + destruct (eq_dec x i); [subst; right; constructor | left].
      unfold Ensembles.In in *.
      rewrite nth_replace_nth' in X; auto.
  - erewrite @iter_sepcon_Znth with (i := Z.of_nat i)(l := upto _)
      by (rewrite Zlength_upto; split; [|apply Nat2Z.inj_lt]; lia).
    erewrite Znth_upto, Znth_replace_nth by lia; iFrame.
    erewrite iter_sepcon_func_strong; auto.
    unfold remove_Znth; intros ? Hin.
    rewrite Znth_replace_nth'; auto.
    intro; subst.
    apply in_app in Hin as [?%In_sublist_upto | ?%In_sublist_upto]; lia.
  - iCombine "en en1" as "en"; erewrite ghost_set_join.
    iDestruct "en" as "[% en]".
    inv H2.
    contradiction (H3 i); constructor; auto; constructor.
Qed.

(* up *)
Lemma replace_nth_same' : forall {A} n l (a d : A), nth n l d = a -> replace_nth n l a = l.
Proof.
  intros; subst; apply replace_nth_same.
Qed.

Lemma wsat_close : forall i P,
  wsat * invariant i P * |> P * ghost_list g_dis (list_singleton i (Some tt)) |--
  (|==> wsat * ghost_set g_en (Ensembles.Singleton i))%I.
Proof.
  intros; unfold wsat, invariant.
  iIntros "(((H & inv1) & HP) & dis1)". iDestruct "H" as (l lg lb) "((((% & inv) & dis) & en) & I)". iDestruct "inv1" as (g) "[snap agree]".
  iAssert (!!(i < length lg /\ Znth (Z.of_nat i) lg = g /\
    exists b, Znth (Z.of_nat i) lb = Some b)%nat) as %Hi.
  { iCombine "snap inv" as "inv"; unfold master_list; erewrite snap_master_join1.
    iDestruct "inv" as "[% inv]".
    apply list_incl_singleton in H0.
    destruct (lt_dec i (length lg));
      [|erewrite nth_overflow in H0 by (erewrite map_length, upto_length; lia); discriminate].
    erewrite nth_map' with (d' := 0) in H0 by (rewrite upto_length; lia).
    erewrite nth_upto in H0 by lia.
    destruct (Znth (Z.of_nat i) lb); inv H0; eauto. }
  iDestruct "snap" as "_".
  iModIntro.
  destruct Hi as (? & ? & b & Hi).
  assert (nth i lb None = Some b) as Hi' by (rewrite <- nth_Znth' in Hi; auto).
  destruct b.
  { iCombine "dis dis1" as "dis".
    iDestruct (own_valid_2(RA := list_PCM _) with "[$dis]") as %H2.
    destruct H2 as (? & J & _).
    apply list_join_nth with (n := i) in J.
    erewrite nth_singleton, nth_map' with (d' := None) in J by lia.
    rewrite Hi' in J; inv J.
    inv H5.
    inv H3. }
  erewrite ghost_set_remove with (a := i).
  iDestruct "en" as "[$ en]".
  iExists l, lg, (replace_nth i lb (Some true)).
  rewrite replace_nth_length predicates_hered.prop_true_andp; last auto.
  iSplitR "I agree HP".
  iSplitR "en".
  iSplitR "dis dis1".
  - erewrite map_ext; [iFrame|].
    intros.
    destruct (eq_dec a (Z.of_nat i)); [subst; rewrite Znth_replace_nth | rewrite Znth_replace_nth'];
      auto; try lia.
    rewrite Hi; auto.
  - iCombine "dis1 dis" as "dis"; setoid_rewrite <- own.ghost_op; [iFrame|].
    rewrite map_replace_nth.
    apply (list_join_singleton(P := token_PCM)).
    { rewrite map_length; lia. }
    erewrite nth_map' with (d' := None) by lia.
    rewrite Hi'; constructor.
  - erewrite Ensembles.Extensionality_Ensembles at 1; [iFrame|]; constructor; intros ? X.
    + inv X; unfold Ensembles.In in *.
      rewrite nth_replace_nth'; auto.
      intro; subst; contradiction.
    + constructor.
      * unfold Ensembles.In in *.
        destruct (eq_dec x i); [subst; auto|].
        rewrite nth_replace_nth' in X; auto.
      * intro X'; inv X'.
        unfold Ensembles.In in X.
        rewrite -> nth_replace_nth in X by lia; inv X.
  - erewrite !iter_sepcon_eq, @iter_sepcon_Znth with (i := Z.of_nat i)
      by (rewrite Zlength_upto; split; [|apply Nat2Z.inj_lt]; lia).
    erewrite @iter_sepcon_Znth with (i := Z.of_nat i)(l := upto _)
      by (rewrite Zlength_upto; split; [|apply Nat2Z.inj_lt]; lia).
    erewrite !Znth_upto, !Znth_replace_nth by lia.
    rewrite Hi.
    iDestruct "I" as "[agree' I]".
    subst; iDestruct (agree_join2 with "[agree' agree]") as "[imp agree]"; first by iFrame.
    iPoseProof ("imp" with "HP") as "?"; iFrame.
    erewrite iter_sepcon_func_strong; eauto.
    unfold remove_Znth; intros ? Hin.
    rewrite Znth_replace_nth'; auto.
    intro; subst.
    apply in_app in Hin as [?%In_sublist_upto | ?%In_sublist_upto]; lia.
  - unfold Ensembles.In; auto.
Qed.

End Invariants.

Lemma make_wsat : emp |-- |==> EX inv_names : invG, wsat.
Proof.
  unfold wsat.
  iIntros.
  iMod (own_alloc(RA := snap_PCM(ORD := list_order gname)) (Tsh, nil) NoneP with "[$]") as (g_inv) "inv"; first (simpl; auto).
  iMod (own_alloc(RA := list_PCM (exclusive_PCM unit)) nil NoneP with "[$]") as (g_dis) "dis"; first (simpl; auto).
  iMod (own_alloc(RA := set_PCM) empty NoneP with "[$]") as (g_en) "en"; first (simpl; auto).
  iModIntro.
  iExists {| g_inv := g_inv; g_dis := g_dis; g_en := g_en |}.
  iExists nil, nil, nil; simpl; iFrame "inv dis en"; auto.
Qed.

Global Instance into_inv_inv N P : IntoInv (inv N P) N := {}.

Lemma inv_nonexpansive : forall N, nonexpansive (inv N).
Proof.
  intros; unfold inv.
  apply @exists_nonexpansive; intros i.
  apply @conj_nonexpansive, invariant_nonexpansive.
  apply const_nonexpansive.
Qed.

Lemma inv_nonexpansive2 : forall N f, nonexpansive f ->
  nonexpansive (fun a => inv N (f a)).
Proof.
  intros; unfold inv.
  apply @exists_nonexpansive; intros i.
  apply @conj_nonexpansive, invariant_nonexpansive2, H.
  apply const_nonexpansive.
Qed.
