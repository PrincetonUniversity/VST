(* modified from iris.algebra.dfrac *)

From stdpp Require Import countable.
From iris.algebra Require Export cmra.
From iris.algebra Require Import updates proofmode_classes.
From iris_ora.algebra Require Export ora.
From iris.prelude Require Import options.
Require Export VST.veric.share_alg.

(** An element of dfrac denotes ownership of a fraction, knowledge that a
    fraction has been discarded, or both. Note that [DfracBoth] can be written
    as [DfracOwn q ⋅ DfracDiscarded]. This should be used instead
    of [DfracBoth] which is for internal use only. *)
Inductive dfrac :=
  | DfracOwn : share → dfrac
  | DfracDiscarded : dfrac
  | DfracBoth : share → dfrac.

(* This notation is intended to be used as a component in other notations that
   include discardable fractions. The notation provides shorthands for the
   constructors and the commonly used full fraction. For an example
   demonstrating how this can be used see the notation in [ghost_map.v]. *)
Declare Custom Entry dfrac.
Notation "{ dq }" := (dq) (in custom dfrac at level 1, dq constr).
Notation "□" := DfracDiscarded (in custom dfrac).
Notation "{# q }" := (DfracOwn q) (in custom dfrac at level 1, q constr).
Notation "" := (DfracOwn Tsh) (in custom dfrac).

Section dfrac.
  Canonical Structure dfracO := leibnizO dfrac.

  Implicit Types p q : share.
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
    | DfracOwn q => q ≠ Share.bot
    | DfracDiscarded => True
    | DfracBoth q => q ≠ Tsh /\ q ≠ Share.bot
    end%Qp.

  (** As in the fractional camera the core is undefined for elements denoting
     ownership of a fraction. For elements denoting the knowledge that a fraction has
     been discarded the core is the identity function. *)
  Local Instance dfrac_pcore_instance : PCore dfrac := λ dq,
    match dq with
    | DfracOwn q => None
    | DfracDiscarded => Some DfracDiscarded
    | DfracBoth q => Some DfracDiscarded
    end.

  Existing Instance share_op_instance.

  (** When elements are combined, ownership is added together and knowledge of
     discarded fractions is combined with the max operation. *)
  Local Instance dfrac_op_instance : Op dfrac := λ dq dp,
    match dq, dp with
    | DfracOwn q, DfracOwn q' => DfracOwn (q ⋅ q')
    | DfracOwn q, DfracDiscarded => DfracBoth q
    | DfracOwn q, DfracBoth q' => DfracBoth (q ⋅ q')
    | DfracDiscarded, DfracOwn q' => DfracBoth q'
    | DfracDiscarded, DfracDiscarded => DfracDiscarded
    | DfracDiscarded, DfracBoth q' => DfracBoth q'
    | DfracBoth q, DfracOwn q' => DfracBoth (q ⋅ q')
    | DfracBoth q, DfracDiscarded => DfracBoth q
    | DfracBoth q, DfracBoth q' => DfracBoth (q ⋅ q')
    end.

  Lemma dfrac_op_own q p : DfracOwn p ⋅ DfracOwn q = DfracOwn (p ⋅ q).
  Proof. done. Qed.

  Lemma dfrac_op_discarded :
    DfracDiscarded ⋅ DfracDiscarded = DfracDiscarded.
  Proof. done. Qed.

  Lemma dfrac_own_included q p : DfracOwn q ≼ DfracOwn p ↔ q ≼ p.
  Proof.
    split.
    - rewrite /included /op /dfrac_op_instance. intros [[o| |?] [= ->]].
      by exists o.
    - intros [o ->]. exists (DfracOwn o). by rewrite dfrac_op_own.
  Qed.

  (* [dfrac] does not have a unit so reflexivity is not for granted! *)
  Lemma dfrac_discarded_included :
    DfracDiscarded ≼ DfracDiscarded.
  Proof. exists DfracDiscarded. done. Qed.

  Definition dfrac_ra_mixin : RAMixin dfrac.
  Proof.
    split; try apply _.
    - intros [?| |?] ? dq <-; intros [= <-]; eexists _; done.
    - intros [?| |?] [?| |?] [?| |?];
        rewrite /op /dfrac_op_instance 1?(assoc_L(A := shareR)); done.
    - intros [?| |?] [?| |?];
        rewrite /op /dfrac_op_instance 1?(comm_L(A := shareR)); done.
    - intros [?| |?] dq; rewrite /pcore /dfrac_pcore_instance; intros [= <-];
        rewrite /op /dfrac_op_instance; done.
    - intros [?| |?] ? [= <-]; done.
    - intros [?| |?] [?| |?] ? [[?| |?] [=]] [= <-]; eexists _; split; try done;
        apply dfrac_discarded_included.
    - intros [q| |q] [q'| |q']; rewrite /op /dfrac_op_instance /valid /dfrac_valid_instance //.
      + by intros (? & ? & ?)%share_valid2_joins.
      + by intros [].
      + by intros [? (? & ? & ?)%share_valid2_joins].
      + intros [? (? & ? & ? & J)%share_valid2_joins]; split; auto.
        intros ->.
        apply join_Tsh in J as []; done.
      + intros [? (? & ? & ? & J)%share_valid2_joins]; split; auto.
        intros ->.
        apply join_Tsh in J as []; done.
  Qed.
  Canonical Structure dfracC := discreteR dfrac dfrac_ra_mixin.

  Global Instance dfrac_cmra_discrete : CmraDiscrete dfracC.
  Proof. apply discrete_cmra_discrete. Qed.

  Global Instance dfrac_full_exclusive : Exclusive (DfracOwn Tsh).
  Proof.
    intros [q| |q];
      rewrite /op /cmra_op -cmra_discrete_valid_iff /valid /cmra_valid //=.
    - intros (? & ? & ? & (? & ?)%join_Tsh)%share_valid2_joins; contradiction.
    - tauto.
    - intros [? (? & ? & ? & (? & ?)%join_Tsh)%share_valid2_joins]; contradiction.
  Qed.

  Global Instance dfrac_cancelable q : Cancelable (DfracOwn q).
  Proof.
    apply: discrete_cancelable.
    intros [q1| |q1][q2| |q2] ? [=]; simplify_eq/=; try done.
    - by apply (share_cancelable _ 0) in H1 as ->.
    - destruct H.
      symmetry in H1; apply share_op_join in H1 as (? & ? & ?); last done.
      contradiction H2; eapply identity_share_bot, sepalg.unit_identity, sepalg.join_comm; eauto.
    - destruct H.
      rewrite H1 in H0.
      apply share_op_join in H1 as (? & ? & ?); last done.
      contradiction H2; eapply identity_share_bot, sepalg.unit_identity, sepalg.join_comm; eauto.
    - by destruct H; apply (share_cancelable _ 0) in H1 as ->.
  Qed.
  Global Instance dfrac_own_id_free q : IdFree (DfracOwn q).
  Proof. intros [q'| |q'] ? [=]. apply share_op_join in H1 as (? & ? & ?); last done.
    contradiction H1; eapply identity_share_bot, sepalg.unit_identity, sepalg.join_comm; eauto.
  Qed.
  Global Instance dfrac_discarded_core_id : CoreId DfracDiscarded.
  Proof. by constructor. Qed.

  Lemma dfrac_valid_own p : ✓ DfracOwn p ↔ (p ≠ Share.bot).
  Proof. done. Qed.
  Lemma dfrac_valid_own_1 : ✓ DfracOwn Tsh.
  Proof. done. Qed.
  Lemma dfrac_validN_own_1 n : ✓{n} DfracOwn Tsh.
  Proof. apply Share.nontrivial. Qed.

  Lemma dfrac_valid_own_r dq q : ✓ (dq ⋅ DfracOwn q) → q ≠ Tsh /\ q ≠ Share.bot.
  Proof.
    destruct dq as [q'| |q']; [|done|].
    - intros (? & ? & ? & J)%share_valid2_joins.
      split; auto; intros ->.
      apply sepalg.join_comm, join_Tsh in J as []; contradiction.
    - intros [? (? & ? & ? & J)%share_valid2_joins].
      split; auto; intros ->.
      apply sepalg.join_comm, join_Tsh in J as []; contradiction.
  Qed.

  Lemma dfrac_valid_own_l dq q : ✓ (DfracOwn q ⋅ dq) → q ≠ Tsh /\ q ≠ Share.bot.
  Proof. rewrite comm. apply dfrac_valid_own_r. Qed.

  Lemma dfrac_valid_discarded : ✓ DfracDiscarded.
  Proof. done. Qed.

  Lemma dfrac_valid_own_discarded q :
    ✓ (DfracOwn q ⋅ DfracDiscarded) ↔ q ≠ Tsh /\ q ≠ Share.bot.
  Proof. done. Qed.

  Global Instance dfrac_is_op q q1 q2 :
    @IsOp shareR q q1 q2 →
    IsOp' (DfracOwn q) (DfracOwn q1) (DfracOwn q2).
  Proof. rewrite /IsOp' /IsOp dfrac_op_own=>-> //. Qed.

  (** Discarding a fraction is a frame preserving update. *)
  Lemma dfrac_discard_update dq : dq ~~> DfracDiscarded.
  Proof.
    intros n [[q'| |q']|]; rewrite -!cmra_discrete_valid_iff //=.
    - apply dfrac_valid_own_r.
    - apply cmra_valid_op_r.
  Qed.

  Local Instance dfrac_order : OraOrder dfrac := λ a b, a = b ∨ a ⋅ DfracDiscarded = b.

  Local Instance discard_increasing : Increasing DfracDiscarded.
  Proof.
    intros ?.
    rewrite /op /dfrac_op_instance; destruct y; hnf; auto.
  Qed.

  Definition dfrac_ora_mixin : DORAMixin dfrac.
  Proof.
    split.
    - rewrite /pcore /dfrac_pcore_instance; intros [| |]; inversion 1; apply _.
    - inversion 1; hnf; auto.
    - intros ??? [?|?] ?; subst.
      + eexists; split; [|hnf]; eauto.
      + destruct x; try discriminate; eexists; split; hnf; eauto.
    - intros ??? [?|?] [?|?]; subst; hnf; auto.
      destruct x; auto.
    - intros ??? [?|?]; subst; hnf; auto.
      right; by rewrite -assoc (comm _ y) assoc.
    - intros ??? [?|?]; subst; auto.
      eapply cmra_valid_op_l; eauto.
    - destruct x; inversion 1; subst; destruct y; eexists; split; hnf; eauto.
  Qed.

  Canonical Structure dfracR := discreteOra dfrac dfrac_ora_mixin.

  Global Instance dfrac_discarded_oracore_id : OraCoreId DfracDiscarded.
  Proof. by constructor. Qed.

  Global Instance dfrac_ora_discrete : OraDiscrete dfracR.
  Proof. apply discrete_ora_discrete. Qed.

End dfrac.

#[global] Hint Resolve dfrac_valid_own_1 dfrac_validN_own_1 : core.
