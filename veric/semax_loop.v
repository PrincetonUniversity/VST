Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.res_predicates.
Require Import VST.veric.external_state.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.veric.Clight_core.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.
Require Import VST.veric.lifting_expr.
Require Import VST.veric.semax.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.semax_conseq.
Require Import VST.veric.Clight_lemmas.

Local Open Scope nat_scope.

Section extensions.
Context `{!VSTGS OK_ty Σ} {OK_spec : ext_spec OK_ty} {CS: compspecs}.

Local Arguments typecheck_expr : simpl never.

Lemma tc_test_eq1:
  forall b i v m,
  mem_auth m ∗ denote_tc_test_eq (Vptr b i) v ⊢
  ⌜Mem.weak_valid_pointer m b (Ptrofs.unsigned i) = true⌝.
Proof.
intros; iIntros "[Hm H]".
destruct v; try done; simpl.
- iDestruct "H" as "[% H]".
  iApply (binop_lemmas4.weak_valid_pointer_dry with "[$Hm $H]").
- unfold test_eq_ptrs.
  destruct (sameblock (Vptr b i) (Vptr b0 i0)).
  + iDestruct "H" as "[H _]".
    iApply (binop_lemmas4.weak_valid_pointer_dry with "[$Hm $H]").
  + iDestruct "H" as "[H _]".
    iDestruct (binop_lemmas4.valid_pointer_dry with "[$Hm $H]") as %?; iPureIntro.
    apply valid_pointer_implies.
    rewrite Z.add_0_r // in H.
Qed.

Lemma semax_ifthenelse:
   forall E Delta P (b: expr) c d R,
      bool_type (typeof b) = true ->
     semax OK_spec E Delta (P ∧ local (expr_true b)) c R ->
     semax OK_spec E Delta (P ∧ local (expr_false b)) d R ->
     semax OK_spec E Delta
              (▷ (tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) ∧ P))
              (Sifthenelse b c d) R.
Proof.
  intros.
  rewrite !semax_unfold in H0, H1 |- *.
  intros; iIntros "#? ? #?" (?) "P".
  destruct HGG.
  iApply wp_if.
  iApply wp_tc_expr; first done.
  iSplit; first done. iSplit.
  { admit. }
  iIntros (bv Ht) "#Hb"; iSplit.
  { admit. }
(*   rewrite (add_and (▷ _) (▷ _)); last by iIntros "[H _]"; iApply (typecheck_expr_sound with "H"). *)
  destruct (bool_val (typeof b) bv) as [b'|] eqn: Hb.
  iExists b'; iSplit; first done.
  rewrite bi.and_elim_r.
  destruct b'; [iApply (H0 with "[] [$]") | iApply (H1 with "[] [$]")]; eauto; iNext; (iSplit; first done);
    iStopProof; split => rho; monPred.unseal; rewrite !monPred_at_intuitionistically;
    iIntros "(#(_ & _ & ->) & _)"; iPureIntro; apply bool_val_strict; try done.
Admitted.

(*Ltac inv_safe H :=
  inv H;
  try solve[match goal with
    | H : semantics.at_external _ _ _ = _ |- _ =>
      simpl in H; congruence
    | H : j_at_external _ _ _ = _ |- _ =>
      simpl in H; congruence
    | H : semantics.halted _ _ _ |- _ =>
      simpl in H; unfold cl_halted in H; contradiction
  end].*)

Lemma semax_seq:
  forall E Delta (R: ret_assert) P Q h t,
  semax OK_spec E Delta P h (overridePost Q R) ->
  semax OK_spec E Delta Q t R ->
  semax OK_spec E Delta P (Clight.Ssequence h t) R.
Proof.
  intros.
  rewrite !semax_unfold in H,H0|-*.
  intros.
  iIntros "#? ? #?" (?) "P".
  iApply wp_seq.
  Check wp_frame. (* frame in believe? use strong_mono, if it was objective? *)
  iApply wp_conseq; last (by iApply (H with "[] [$]")); destruct R; simpl; auto.
  iIntros "(Q & #? & ?) !>"; iApply (H0 with "[] [$]"); eauto.
  admit.
Admitted.

Lemma semax_loop:
forall E Delta Q Q' incr body R,
     semax OK_spec E Delta Q body (loop1_ret_assert Q' R) ->
     semax OK_spec E Delta Q' incr (loop2_ret_assert Q R) ->
     semax OK_spec E Delta Q (Sloop body incr) R.
Proof.
  intros ?????? POST H H0.
  rewrite semax_unfold.
  intros ?????.
  iLöb as "IH". (* we might in theory want to iLob objectively *)
  iIntros "#? ? #?" (?) "Q".
  iApply wp_loop.
  (* this should also be <obj>? *)
  iAssert (Q' ∗ <affine> local (typecheck_environ Delta') ∗ funassert Delta'
    -∗ |={E}=>
    wp OK_spec psi E f incr
      (loop2_ret_assert
         (wp OK_spec psi E f (Sloop body incr)
            (frame_ret_assert POST
               (<affine> local (typecheck_environ Delta') ∗ funassert Delta')))
         (frame_ret_assert POST
            (<affine> local (typecheck_environ Delta') ∗ funassert Delta'))))%I as "H".
  { iIntros "(? & _ & ?) !>"; iApply wp_conseq; last (by iApply (H0 with "[%] [$] [$]")); simpl; auto.
    - (* lost IH; probably need strong_mono *) admit.
    - iIntros "([] & _ & _)". }
  iNext; iApply wp_conseq; last (by iApply (H with "[%] [$] [$]")); simpl; auto.
  - admit.
  - admit.
Admitted.

Lemma semax_break:
   forall E Delta Q,        semax OK_spec E Delta (RA_break Q) Sbreak Q.
Proof.
  intros.
  rewrite semax_unfold; intros.
  iIntros "???" (?) "?".
  iApply wp_break; by iFrame.
Qed.

Lemma semax_continue:
   forall E Delta Q,        semax OK_spec E Delta (RA_continue Q) Scontinue Q.
Proof.
  intros.
  rewrite semax_unfold; intros.
  iIntros "???" (?) "?".
  iApply wp_continue; by iFrame.
Qed.

End extensions.
