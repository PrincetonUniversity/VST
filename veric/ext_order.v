Require Import iris.algebra.cmra.
Require Import iris_ora.algebra.ora.

(* inclusion order *)
Section incl.

Context {A : cmra} `{CmraTotal A}.

Instance incl_orderN : OraOrderN A := includedN.
Instance incl_order : OraOrder A := λ x y, ∀n, x ≼{n} y.

Instance incl_increasing x : Increasing x.
Proof.
  intros ?; eexists.
  by rewrite comm.
Qed.

Context (inclN_extend : forall n (a b : A), a ≼{n} b -> {c | c ≼{S n} b /\ c ≡{n}≡ a} ).

Definition incl_ora_mixin : OraMixin A.
Proof.
  split; try apply _.
  - intros ????? Hcore.
    eapply cmra_pcore_monoN'; eauto.
    by rewrite Hcore.
  - intros ????? Hord.
    apply inclN_extend in Hord as (? & ? & Heq).
    apply cmra_extend in Heq as (z1 & z2 & Heq & ? & ?).
    exists z1, z2; rewrite -Heq; auto.
    { eapply cmra_validN_includedN; eauto using cmra_includedN_S. }
  - intros; apply inclN_extend; auto.
  - intros ??? ->.
    exists (core y); by rewrite cmra_core_r.
  - intros; by apply cmra_includedN_S.
  - intros; by apply cmra_monoN_r.
  - intros; by eapply cmra_validN_includedN.
  - reflexivity.
  - intros ??? Hcore.
    inversion Hcore as [?? Heq Hcore1|]; subst.
    symmetry in Hcore1; eapply cmra_pcore_mono in Hcore1 as (? & -> & ?); last by eexists.
    eexists; split; first done.
    by intros ?; rewrite -Heq; apply cmra_included_includedN.
Qed.

(*Canonical Structure inclR : ora := Ora A incl_ora_mixin.*)

Global Instance incl_ora_total : OraTotal (Ora A incl_ora_mixin).
Proof. rewrite /OraTotal; eauto. Qed.

End incl.

Section flat.

Context {A : cmra} (core_identity : forall (a ca b : A), pcore a = Some ca -> ca ⋅ b ≡ b).

Lemma core_equiv : forall (a b ca cb : A), pcore a = Some ca -> pcore b = Some cb -> ca ≡ cb.
Proof.
  intros.
  etrans; [symmetry; eapply core_identity; done|].
  rewrite comm; eauto.
Qed.

Lemma core_flat : forall (a ca b : A), pcore a = Some ca -> pcore (a ⋅ b) ≡ Some ca.
Proof.
  intros.
  edestruct (cmra_pcore_mono a (a ⋅ b)) as (? & Hcore & _); [eexists | |]; try done.
  rewrite Hcore; constructor; eapply core_equiv; eauto.
Qed.

Instance flat_orderN : OraOrderN A := dist.
Instance flat_order : OraOrder A := equiv.

(*Lemma Increasing_inv : forall (a : A), Increasing*)

Definition flat_ora_mixin : OraMixin A.
Proof.
  split; try apply _; try done.
  - intros ????.
    by rewrite core_identity.
  - intros ??????.
    admit. (* should we only know Increasing for orderN here? or do we need another axiom? *)
  - apply cmra_pcore_ne.
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
    inversion H as [?? Heq|]; subst.
    by rewrite -Heq; apply core_flat.
Admitted.

(*Canonical Structure flatR : ora := Ora A flat_ora_mixin.*)

End flat.
