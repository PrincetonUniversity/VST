Require Import iris.algebra.cmra.
Require Import iris_ora.algebra.ora.

(* inclusion order *)
Section incl.

Context {A : cmra} `{CmraTotal A}.

Instance incl_orderN : OraOrderN A := fun n x y => ∃y1, x ≼ y1 /\ y1 ≡{n}≡ y.
(* Instance incl_order : OraOrder A := (≼). *) (* don't think this satisfies order_orderN *)
Instance incl_order : OraOrder A := fun x y => forall n, incl_orderN n x y.

Definition incl_ora_mixin : OraMixin A.
Proof.
  split; try apply _.
  - apply cmra_pcore_ne.
  - intros ?????.
    eexists; split; last done.
    apply cmra_included_r.
  - intros ???????.
    eexists; split; last done.
    apply cmra_included_r.
  - apply cmra_valid_validN.
  - apply cmra_validN_S.
  - apply cmra_pcore_l.
  - apply cmra_pcore_idemp.
  - intros ???? (? & ? & ?) Hcore.
    eapply cmra_pcore_mono in Hcore as (? & Hcore & ?); last done.
    eapply cmra_pcore_ne in Hcore as (? & Hcore & ?); last done.
    eexists; split; [|eexists]; done.
  - apply cmra_validN_op_l.
  - intros ????? (? & (? & Heq) & Hdist).
    rewrite Heq in Hdist; symmetry in Hdist.
    apply cmra_extend in Hdist as (z & ? & Heq1 & Hz & ?); last done.
    apply cmra_extend in Hz as (z1 & z2 & Heq2 & ? & ?).
    exists z1, z2; split; try done.
    eexists; split; last done.
    rewrite Heq1 -Heq2; apply cmra_included_l.
    { eapply cmra_validN_included; first done. rewrite Heq1; apply cmra_included_l. }
  - intros ???? (? & (? & Heq) & Hdist).
    rewrite Heq in Hdist; symmetry in Hdist.
    apply cmra_extend in Hdist as (z & ? & Heq1 & Hz & ?); last done.
    exists z; split; [exists x; split|]; try done.
    rewrite Heq1; apply cmra_included_l.
  - intros; eexists; done.
  - intros ??? (? & ? & ?%dist_S).
    eexists; done.
  - intros ???? (? & Hincl1 & ?) (? & Hincl2 & ?).
    eapply cmra_included_dist_l in Hincl2 as (? & ? & ?); last done.
    eexists; split; etrans; done.
  - intros ???? (? & ? & Hdist).
    eexists; split; [apply cmra_mono; done|].
    by rewrite Hdist.
  - intros ??? Hvalid (? & ? & Hdist).
    rewrite -Hdist in Hvalid; eapply cmra_validN_included; done.
  - reflexivity.
  - intros ??? Hcore.
    destruct (pcore x) eqn: Hcx; inversion Hcore as [?? Heq|]; subst.
    edestruct (cmra_pcore_mono x (x ⋅ y)) as (? & -> & Hincl); try done.
    { apply cmra_included_l. }
    rewrite Heq in Hincl.
    eexists; split; first done.
    intros ?; eexists; done.
Qed.

Canonical Structure inclR : oraT := OraT A incl_ora_mixin.

Global Instance incl_ora_total : OraTotal inclR.
Proof. rewrite /OraTotal; eauto. Qed.

End incl.

Section flat.

Context {A : cmra} (Hcore : forall (a ca : A), pcore a = Some ca -> forall b, ca ⋅ b ≡ b)
  (Hflat : forall (a b ca : A), pcore a = Some ca -> pcore (a ⋅ b) ≡ Some ca).

Instance flat_orderN : OraOrderN A := dist.
Instance flat_order : OraOrder A := equiv.

Definition flat_ora_mixin : OraMixin A.
Proof.
  split; try apply _; try done.
  - apply cmra_pcore_ne.
  - intros ????.
    by rewrite Hcore.
  - intros ???? Heq ?.
    admit. (* I think this axiom is wrong: we should only know Increasing for the step-indexed order *)
  - apply cmra_valid_validN.
  - apply cmra_validN_S.
  - apply cmra_pcore_l.
  - apply cmra_pcore_idemp.
  - apply cmra_pcore_ne.
  - apply cmra_validN_op_l.
  - intros ????? Hdist.
    symmetry in Hdist; apply cmra_extend in Hdist as (z & ? & Heq1 & Hz & ?); last done.
    eexists _, _; split; last done.
    by rewrite Heq1.
  - eauto.
  - apply dist_S.
  - by intros ???? ->.
  - by intros ???? ->.
  - apply equiv_dist.
  - intros.
    eexists; split; last done.
    destruct (pcore x) eqn: ?; inversion H; subst.
    rewrite -H; auto.
Admitted.

Canonical Structure flatR : oraT := OraT A flat_ora_mixin.

End flat.
