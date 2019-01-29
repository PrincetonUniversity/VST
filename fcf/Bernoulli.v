(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

Set Implicit Arguments.

Require Import FCF.Crypto.
Require Import FCF.RndNat.
Require Import FCF.NotationV1.

Definition Bernoulli(r : Rat) : Comp bool :=
  match r with
    | RatIntro n d =>
      v <-$ RndNat d; ret (if (lt_dec v n) then true else false)
  end.


Theorem Bernoulli_correct : 
  forall (r : Rat),
    r <= 1 ->
    Pr[Bernoulli r] == r.

  unfold Bernoulli.
  intuition.
  destruct r.

  rewrite RndNat_seq.
  
  rewrite (sumList_filter_partition (fun z => if (lt_dec z n) then true else false)).
  eapply eqRat_trans.
  eapply ratMult_eqRat_compat.
  eapply eqRat_refl.
  eapply ratAdd_eqRat_compat.

  eapply sumList_all.
  intros.
  destruct ( lt_dec a n).
  simpl.
  destruct ( EqDec_dec bool_EqDec true true).
  eapply eqRat_refl.
  intuition.
  apply filter_In in H0.
  intuition.
  exfalso.
  destruct (lt_dec a n); intuition.

  eapply sumList_0.
  intros.
  apply filter_In in H0.
  intuition.
  destruct (lt_dec a n); simpl in *.
  discriminate.
  destruct (EqDec_dec bool_EqDec false true); intuition.

  rewrite allNatsLt_filter_lt.
  rewrite <- ratAdd_0_r.
  rewrite ratMult_1_r.
  rewrite allNatsLt_length.
  rewrite <- ratMult_num_den.
  eapply eqRat_terms.
  omega.
  unfold posnatMult, posnatToNat, natToPosnat.
  destruct p.
  omega.

  eapply rat_le_1_if; trivial.

Qed.

Theorem Bernoulli_wf : 
  forall r, 
    well_formed_comp (Bernoulli r).

  intuition.
  unfold Bernoulli.
  destruct r.
  wftac.

Qed.

Theorem Bernoulli_correct_complement : 
  forall (r : Rat),
    r <= 1 ->
    evalDist (Bernoulli r) false == 
    ratSubtract 1 r.

  intuition.
  eapply eqRat_trans.
  eapply evalDist_complement.
  eapply Bernoulli_wf.
  eapply ratSubtract_eqRat_compat; intuition.
  eapply Bernoulli_correct.
  trivial.
Qed.
