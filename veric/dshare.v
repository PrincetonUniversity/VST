(* modified from iris.algebra.dfrac *)

From stdpp Require Import countable.
From iris.algebra Require Export cmra.
From iris.algebra Require Import updates proofmode_classes.
From iris_ora.algebra Require Export ora.
From iris.prelude Require Import options.
Require Export VST.veric.share_alg.

(** Since shares have a unit, we use DfracBoth Share.bot as the persistent fraction. *)
Inductive dfrac :=
  | DfracOwn : shareO → dfrac (* Would it make sense to have a separate constructor for unreadable shares? *)
  | DfracBoth : shareO → dfrac.

Definition DfracDiscarded := DfracBoth (Share Share.bot).

(* This notation is intended to be used as a component in other notations that
   include discardable fractions. The notation provides shorthands for the
   constructors and the commonly used full fraction. For an example
   demonstrating how this can be used see the notation in [ghost_map.v]. *)
Declare Custom Entry dfrac.
Notation "{ dq }" := (dq) (in custom dfrac at level 1, dq constr).
Notation "□" := DfracDiscarded (in custom dfrac).
Notation "{# q }" := (DfracOwn (Share q)) (in custom dfrac at level 1, q constr).
Notation "" := (DfracOwn (Share Tsh)) (in custom dfrac).

Section dfrac.
  Canonical Structure dfracO := leibnizO dfrac.

  Implicit Types p q : shareO.
  Implicit Types dp dq : dfrac.

  Global Instance dfrac_inhabited : Inhabited dfrac := populate DfracDiscarded.
  Global Instance dfrac_eq_dec : EqDecision dfrac.
  Proof. solve_decision. Defined.
(*  Global Instance dfrac_countable : Countable dfrac.
  Proof.
    set (enc dq := match dq with
      | DfracOwn q => inl q
      | DfracDiscarded => inr (inl ())
      | DfracBoth q => inr (inr q)
      end).
    set (dec y := Some match y with
      | inl q => DfracOwn q
      | inr (inl ()) => DfracDiscarded
      | inr (inr q) => DfracBoth q
      end).
    refine (inj_countable enc dec _). by intros [].
  Qed.*)

  Global Instance DfracOwn_inj : Inj (=) (=) DfracOwn.
  Proof. by injection 1. Qed.
  Global Instance DfracBoth_inj : Inj (=) (=) DfracBoth.
  Proof. by injection 1. Qed.

  Local Instance dfrac_valid_instance : Valid dfrac := λ dq,
    match dq with
    | DfracOwn q => ✓ q
    | DfracBoth q => ∃ sh, q = Share sh ∧ ¬writable0_share sh
    end%Qp.

  Local Instance dfrac_pcore_instance : PCore dfrac := λ dq, Some
    match dq with
    | DfracOwn q => DfracOwn (core q)
    | DfracBoth q => DfracBoth (core q)
    end.

  Local Instance dfrac_op_instance : Op dfrac := λ dq dp,
    match dq, dp with
    | DfracOwn q, DfracOwn q' => DfracOwn (q ⋅ q')
    | DfracOwn q, DfracBoth q' => DfracBoth (q ⋅ q')
    | DfracBoth q, DfracOwn q' => DfracBoth (q ⋅ q')
    | DfracBoth q, DfracBoth q' => DfracBoth (q ⋅ q')
    end.

  Lemma dfrac_op_own q p : DfracOwn p ⋅ DfracOwn q = DfracOwn (p ⋅ q).
  Proof. done. Qed.

  Lemma dfrac_op_discarded :
    DfracDiscarded ⋅ DfracDiscarded = DfracDiscarded.
  Proof. rewrite /op /dfrac_op_instance /= left_id //. Qed.

  Lemma dfrac_op_own_discarded q : DfracOwn q ⋅ DfracDiscarded = DfracBoth q.
  Proof. rewrite /op /= right_id //. Qed.

  Lemma dfrac_op_both_discarded q : DfracBoth q ⋅ DfracDiscarded = DfracBoth q.
  Proof. rewrite /op /= right_id //. Qed.

  Lemma dfrac_included_eq dq dp : dq ≼ dp ↔ match dq, dp with
    | DfracOwn q, DfracOwn p | DfracOwn q, DfracBoth p | DfracBoth q, DfracBoth p => q ≼ p
    | _, _ => False
    end.
  Proof.
    destruct dq as [q|q], dp as [p|p].
    - split; last by (intros [o ->]; exists (DfracOwn o)).
      intros [[?|?] [= ->]]; by eexists.
    - split; last by (intros [o ->]; exists (DfracBoth o)).
      intros [[?|?] [= ->]]; try done.
      by eexists.
    - split; last done.
      intros [[?|?] [= ->]]; done.
    - split; last by (intros [o ->]; exists (DfracOwn o)).
      intros [[?|?] [= ->]]; try done; by eexists.
  Qed.

  Definition dfrac_ra_mixin : RAMixin dfrac.
  Proof.
    apply ra_total_mixin; try apply _; try done.
    - intros [?|?] [?|?] [?|?];
        rewrite /op /dfrac_op_instance 1?(assoc_L(A := shareR)); done.
    - intros [?|?] [?|?];
        rewrite /op /dfrac_op_instance 1?(comm_L(A := shareR)); done.
    - intros [?|?]; rewrite /core /pcore /dfrac_pcore_instance /=;
        rewrite /op /dfrac_op_instance ?cmra_core_l //.
    - intros [?|?]; rewrite /core /pcore /dfrac_pcore_instance /= ?cmra_core_idemp //.
    - intros [?|?] [?|?]; rewrite !dfrac_included_eq /=; try done; apply (cmra_core_mono(A := shareR)).
    - intros [q|q] [q'|q']; rewrite /op /dfrac_op_instance /valid /dfrac_valid_instance //.
      + apply cmra_valid_op_l.
      + intros (? & H & ?); eapply cmra_valid_op_l; setoid_rewrite H; done.
      + intros (? & (? & ? & -> & -> & J)%share_op_join & ?).
        eexists; split; first done.
        intros X; apply join_writable01 in J; auto.
      + intros (? & (? & ? & -> & -> & J)%share_op_join & ?).
        eexists; split; first done.
        intros X; apply join_writable01 in J; auto.
  Qed.
  Canonical Structure dfracC := discreteR dfrac dfrac_ra_mixin.

  Global Instance dfrac_cmra_total : CmraTotal dfracC.
  Proof. hnf; eauto. Qed.
  Global Instance dfrac_cmra_discrete : CmraDiscrete dfracC.
  Proof. apply discrete_cmra_discrete. Qed.

  Global Instance dfrac_cancelable q : Cancelable (DfracOwn q).
  Proof.
    apply: discrete_cancelable.
    intros [q1|q1] [q2|q2] ? [=]; simplify_eq/=; try done.
    - by apply (share_cancelable _ 0) in H1 as ->.
    - destruct H as (? & J & ?).
      apply (share_cancelable _ 0) in H1 as ->; try done.
      rewrite J; hnf; eauto.
  Qed.

  Local Instance dfrac_unit : Unit dfrac := DfracOwn (Share Share.bot).

  Lemma dfrac_full_exclusive : ∀ dq, ✓ (DfracOwn (Share Tsh) ⋅ dq) → dq = ε.
  Proof.
    intros [q|q]; rewrite /op /=.
    - intros (? & ? & ? & [=] & -> & ? & J)%share_valid2_joins; subst.
      apply join_Tsh in J as (-> & ->); done.
    - intros (? & (? & ? & [=] & -> & J)%share_op_join & ?); subst.
      apply join_Tsh in J as (-> & ->).
      contradiction H; apply writable_writable0; auto.
  Qed.

  Definition dfrac_ucmra_mixin : UcmraMixin dfrac.
  Proof.
    split; try done.
    intros [|]; rewrite /op /dfrac_op_instance /= left_id //.
  Qed.
  Canonical Structure dfracUC := Ucmra dfrac dfrac_ucmra_mixin.

  Lemma dfrac_valid_own_1 : ✓ DfracOwn (Share Tsh).
  Proof. hnf; eauto. Qed.

(*  Lemma dfrac_valid_own_r dq q : ✓ (dq ⋅ DfracOwn q) → exists sh, q = Some sh ∧ sh ≠ Tsh.
  Proof.
    destruct dq as [q'| |q'].
    - intros (? & ? & ? & -> & -> & ? & J)%share_valid2_joins.
      eexists; split; first done; intros ->.
      apply sepalg.join_comm, join_Tsh in J as [].
    - intros [H ?]; split; intros ?; subst; try done.
      contradiction H; by apply writable_writable0.
    - intros [? (? & ? & J)%share_valid2_joins].
      split; auto; intros ->.
      apply sepalg.join_comm, join_Tsh in J as []; contradiction.
  Qed.

  Lemma dfrac_valid_own_l dq q : ✓ (DfracOwn q ⋅ dq) → q ≠ Tsh /\ q ≠ Share.bot.
  Proof. rewrite comm. apply dfrac_valid_own_r. Qed.*)

  Lemma dfrac_valid_discarded : ✓ DfracDiscarded.
  Proof.
    hnf.
    eexists; split; first done.
    intros ?%writable0_readable; contradiction bot_unreadable.
  Qed.

  Lemma dfrac_valid_own_discarded q :
    ✓ (DfracOwn q ⋅ DfracDiscarded) ↔ ∃ sh, q = Share sh ∧ ~writable0_share sh.
  Proof.
    rewrite /op /= /valid /=.
    rewrite right_id //.
  Qed.

  Definition readable_dfrac (dq : dfrac) :=
    match dq with DfracOwn (Share sh) => readable_share sh | DfracBoth (Share _) => True | _ => False end.

  Lemma dfrac_valid_own_readable dq q : readable_dfrac dq ->
    ✓ (dq ⋅ DfracOwn q) → ∃ sh, q = Share sh ∧ ¬writable0_share sh.
  Proof.
    intros Hdq; destruct dq as [q'|q']; try done.
    - intros (? & ? & ? & -> & -> & ? & J)%share_valid2_joins.
      eexists; split; first done.
      intros ?; apply sepalg.join_comm in J; eapply join_writable0_readable; eauto.
    - intros (? & (? & ? & -> & -> & J)%share_op_join & ?).
      eexists; split; first done.
      intros X; apply sepalg.join_comm in J; contradiction H; eapply join_writable01; eauto.
  Qed.

  Global Instance dfrac_is_op q q1 q2 :
    @IsOp shareR q q1 q2 →
    IsOp' (DfracOwn q) (DfracOwn q1) (DfracOwn q2).
  Proof. rewrite /IsOp' /IsOp dfrac_op_own=>-> //. Qed.

  (** Discarding a fraction is a frame preserving update. *)
  Lemma dfrac_discard_update dq : readable_dfrac dq -> dq ~~> DfracDiscarded.
  Proof.
    intros H n [[q'|q']|]; rewrite -!cmra_discrete_valid_iff //=.
    - intros; rewrite comm dfrac_valid_own_discarded.
      by eapply dfrac_valid_own_readable.
    - intros ?%cmra_valid_op_r.
      rewrite comm dfrac_op_both_discarded //.
    - intros; apply dfrac_valid_discarded.
  Qed.

  Local Instance dfrac_order : OraOrder dfrac := λ a b, a = b ∨ a ⋅ DfracDiscarded = b.

  Local Instance discard_increasing : Increasing DfracDiscarded.
  Proof.
    intros [|]; [right | left].
    - rewrite (comm op) //.
    - rewrite (comm op) dfrac_op_both_discarded //.
  Qed.

  Definition dfrac_ora_mixin : DORAMixin dfrac.
  Proof.
    apply dora_total_mixin; try done.
    - intros [|]; inversion 1; subst; try apply _.
      intros ?.
      rewrite left_id; by left.
    - inversion 1; hnf; auto.
    - intros ?? [?|?]; subst.
      + by left.
      + right; destruct x; rewrite /op /= left_id //.
    - intros ??? [?|?] [?|?]; subst; hnf; auto.
      right; destruct x; rewrite !dfrac_op_both_discarded //.
    - intros ??? [?|?]; subst; hnf; auto.
      right; by rewrite -assoc (comm _ y) assoc.
    - intros ??? [?|?]; subst; auto.
      eapply cmra_valid_op_l; eauto.
    - destruct x; inversion 1 as [?? Hcore|]; subst; rewrite -Hcore; destruct y; eexists; split; hnf; eauto.
      rewrite dfrac_op_own_discarded //.
  Qed.

  Canonical Structure dfracR := discreteOra dfrac dfrac_ora_mixin.
  Canonical Structure dfracUR := Uora dfrac dfrac_ucmra_mixin.

  Global Instance dfrac_discarded_oracore_id : OraCoreId DfracDiscarded.
  Proof. by constructor. Qed.

  Global Instance dfrac_ora_total : OraTotal dfracR.
  Proof. hnf; eauto. Qed.
  Global Instance dfrac_ora_discrete : OraDiscrete dfracR.
  Proof. apply discrete_ora_discrete. Qed.

End dfrac.

#[global] Hint Resolve dfrac_valid_own_1 : core.
