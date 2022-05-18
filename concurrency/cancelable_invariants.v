(* recapitulate iris/base_logic/lib/cancelable_invariants.v *)
Require Import VST.msl.shares.
Require Import VST.veric.shares.
Require Import VST.msl.ghost.
Require Import VST.msl.ghost_seplog.
Require Import VST.veric.invariants.
Require Import VST.concurrency.conclib.

#[export] Program Instance share_ghost : Ghost := { G := share; valid _ := True }.

Definition cinv_own g sh := own(RA := share_ghost) g sh compcert_rmaps.RML.R.NoneP.

Definition cinvariant i g P := invariant i (P || cinv_own g Tsh).

Lemma cinv_alloc' : forall P, wsat * |> P |-- |==> wsat * EX i : _, EX g : _, cinvariant i g P * cinv_own g Tsh.
Proof.
  intros.
  rewrite <- emp_sepcon at 1.
  eapply derives_trans; [eapply derives_trans, bupd_frame_r|].
  { apply sepcon_derives, derives_refl.
    apply (own_alloc(RA := share_ghost)), I. }
  eapply derives_trans, bupd_trans; apply bupd_mono.
  Intros g.
  eapply derives_trans; [eapply derives_trans; [|apply sepcon_derives, derives_refl; unseal_derives; apply wsat_alloc]|].
  2: { unseal_derives; eapply predicates_hered.derives_trans, own.bupd_mono; [apply own.bupd_frame_r|].
       rewrite exp_sepcon2, predicates_sl.exp_sepcon2.
       rewrite predicates_sl.exp_sepcon1.
       apply predicates_hered.exp_derives; intros.
       rewrite predicates_sl.sepcon_assoc.
       apply predicates_sl.sepcon_derives; [apply predicates_hered.derives_refl|].
       eapply predicates_hered.exp_right, predicates_hered.derives_refl. }
  rewrite sepcon_comm; apply sepcon_derives, derives_refl.
  change predicates_sl.sepcon with sepcon; apply sepcon_derives; [apply derives_refl|].
  change (predicates_hered.box predicates_hered.laterM) with later; apply later_derives, orp_right1, derives_refl.
Qed.

Corollary cinv_alloc : forall E P, |> P |-- |={E}=> EX i : _, EX g : _, cinvariant i g P * cinv_own g Tsh.
Proof.
  intros.
  apply wsat_fupd, cinv_alloc'.
Qed.

Lemma cinv_cancel' : forall E i g P, cinvariant i g P * cinv_own g Tsh |-- |={E}=> |> P.
Proof.
  intros; unfold cinvariant.
(*  apply wsat_open.*)
Admitted.

Corollary cinv_cancel : forall E i g P, cinvariant i g P * cinv_own g Tsh |-- |={E}=> |> P.
Proof.
  intros.
  apply wsat_fupd, cinv_cancel'.
Qed.

Lemma cinv_open : forall i P,
  wsat * cinvariant i P * ghost_set g_en (Ensembles.Singleton i) |--
  (|==> wsat * |> P * ghost_list g_dis (list_singleton i (Some tt)))%I.
Proof.
(* apply wsat_open. *)
Admitted.

(*Lemma wsat_close : forall i P,
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
Qed.*)

(*Lemma cinvariant_nonexpansive : forall N, nonexpansive (cinvariant N).
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
Qed.*)

Lemma cinvariant_super_non_expansive : forall i g R n, compcert_rmaps.RML.R.approx n (cinvariant i g R) =
  compcert_rmaps.RML.R.approx n (cinvariant i g (compcert_rmaps.RML.R.approx n R)).
Proof.
  intros; unfold cinvariant.
  rewrite invariant_super_non_expansive; setoid_rewrite invariant_super_non_expansive at 2; do 2 f_equal.
  rewrite !approx_orp; f_equal.
  rewrite approx_idem; auto.
Qed.
