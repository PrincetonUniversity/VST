(* recapitulate iris/base_logic/lib/cancelable_invariants.v *)
Require Import Ensembles.
Require Import VST.msl.shares.
Require Import VST.veric.shares.
Require Import VST.msl.ghost.
Require Import VST.msl.ghost_seplog.
Require Import VST.veric.invariants.
Require Import VST.veric.fupd.
Require Import VST.concurrency.conclib.

#[export] Program Instance share_ghost : Ghost := { G := share; valid _ := True }.

Definition cinv_own g sh := own(RA := share_ghost) g sh compcert_rmaps.RML.R.NoneP.

Definition cinvariant i g P := invariant i (P || cinv_own g Tsh).

Lemma cinvariant_dup : forall i g P, cinvariant i g P = cinvariant i g P * cinvariant i g P.
Proof.
  intros; apply invariant_dup.
Qed.

Lemma cinv_alloc_dep : forall E P, (ALL i g, |> P i g) |-- |={E}=> EX i : _, EX g : _, cinvariant i g (P i g) * cinv_own g Tsh.
Proof.
  intros.
  rewrite <- emp_sepcon at 1.
  sep_eapply (own_alloc(RA := share_ghost)).
  sep_apply bupd_frame_r.
  eapply derives_trans, fupd_trans.
  eapply derives_trans, bupd_fupd; apply bupd_mono.
  Intros g.
  eapply derives_trans; [eapply sepcon_derives, derives_trans, inv_alloc_dep; [apply derives_refl|]|].
  2: { sep_eapply fupd_frame_l; apply fupd_mono.
       Intros i; Exists i g.
       rewrite sepcon_comm; apply derives_refl. }
  apply allp_derives; intros.
  apply allp_left with g.
  apply later_derives, orp_right1, derives_refl.
Qed.

Lemma cinv_alloc : forall E P, |> P |-- |={E}=> EX i : _, EX g : _, cinvariant i g P * cinv_own g Tsh.
Proof.
  intros; eapply derives_trans, cinv_alloc_dep.
  do 2 (apply allp_right; intros); auto.
Qed.

Lemma cinv_own_excl : forall g sh, sh <> Share.bot -> cinv_own g Tsh * cinv_own g sh |-- FF.
Proof.
  intros; unfold cinv_own; sep_apply own_valid_2; Intros.
  destruct H0 as (? & J & ?).
  apply join_Tsh in J as []; contradiction.
Qed.

Lemma cinv_cancel : forall E i g P, Ensembles.In E i -> cinvariant i g P * cinv_own g Tsh |-- |={E}=> |> P.
Proof.
  intros.
  unfold cinvariant.
  sep_apply (inv_open E).
  sep_apply fupd_frame_r; apply fupd_elim.
  rewrite later_orp, !distrib_orp_sepcon; apply orp_left.
  - sep_apply (modus_ponens_wand' (cinv_own g Tsh)).
    { apply orp_right2, now_later. }
    sep_apply fupd_frame_r; rewrite emp_sepcon; auto.
  - eapply derives_trans, except_0_fupd.
    apply orp_right1.
    rewrite sepcon_assoc; eapply derives_trans; [apply sepcon_derives, now_later; apply derives_refl|].
    rewrite <- later_sepcon; apply later_derives.
    sep_apply cinv_own_excl; auto with share.
    rewrite FF_sepcon; auto.
Qed.

Lemma cinv_open : forall E sh i g P, sh <> Share.bot -> Ensembles.In E i ->
  cinvariant i g P * cinv_own g sh |-- |={E, Ensembles.Subtract E i}=> |> P * cinv_own g sh * (|> P -* |={Ensembles.Subtract E i, E}=> emp).
Proof.
  intros.
  unfold cinvariant.
  sep_apply (inv_open E).
  sep_apply fupd_frame_r; apply fupd_elim.
  rewrite later_orp, !distrib_orp_sepcon; apply orp_left.
  - eapply derives_trans, fupd_intro; cancel.
    apply wand_derives; auto.
    apply orp_right1; auto.
  - eapply derives_trans, except_0_fupd.
    apply orp_right1.
    rewrite sepcon_assoc; eapply derives_trans; [apply sepcon_derives, now_later; apply derives_refl|].
    rewrite <- later_sepcon; apply later_derives.
    rewrite (sepcon_comm _ (cinv_own g sh)), <- sepcon_assoc.
    sep_apply cinv_own_excl.
    rewrite FF_sepcon; auto.
Qed.

Lemma cinvariant_nonexpansive : forall i g, nonexpansive (cinvariant i g).
Proof.
  intros; apply invariant_nonexpansive2.
  apply @disj_nonexpansive, const_nonexpansive.
  apply identity_nonexpansive.
Qed.

Lemma cinvariant_nonexpansive2 : forall i g f, nonexpansive f ->
  nonexpansive (fun a => cinvariant i g (f a)).
Proof.
  intros; apply invariant_nonexpansive2.
  apply @disj_nonexpansive, const_nonexpansive; auto.
Qed.

Lemma cinvariant_super_non_expansive : forall i g R n, compcert_rmaps.RML.R.approx n (cinvariant i g R) =
  compcert_rmaps.RML.R.approx n (cinvariant i g (compcert_rmaps.RML.R.approx n R)).
Proof.
  intros; unfold cinvariant.
  rewrite invariant_super_non_expansive; setoid_rewrite invariant_super_non_expansive at 2; do 2 f_equal.
  rewrite !approx_orp; f_equal.
  rewrite approx_idem; auto.
Qed.
