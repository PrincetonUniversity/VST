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

Definition incl_ora_mixin : OraMixin A.
Proof.
  apply ora_total_mixin; try apply _; try done.
  - apply cmra_core_monoN.
  - intros ????? [? Heq].
    apply cmra_extend in Heq as (z & ? & Heq & Hz & ?); auto.
    apply cmra_extend in Hz as (z1 & z2 & Hz & ? & ?); auto.
    exists z1, z2; rewrite Heq -Hz; split; [eexists|]; eauto.
    { eapply cmra_validN_includedN, cmra_includedN_S; eauto.
      rewrite Heq; eexists; eauto. }
  - intros ???? [? Heq].
    apply cmra_extend in Heq as (z & ? & Heq & Hz & ?); auto.
    exists z; rewrite Heq; split; [eexists|]; eauto.
  - intros ??? ->.
    exists (core y); by rewrite cmra_core_r.
  - intros; by apply cmra_includedN_S.
  - intros; by apply cmra_monoN_r.
  - intros; by eapply cmra_validN_includedN.
  - intros ??? Hcore.
    inversion Hcore as [?? Heq Hcore1|]; subst.
    symmetry in Hcore1; eapply cmra_pcore_mono in Hcore1 as (? & -> & ?); last by eexists.
    eexists; split; first done.
    by intros ?; rewrite -Heq; apply cmra_included_includedN.
Qed.

(*Local Canonical Structure inclR : ora := Ora A incl_ora_mixin.*)

Global Instance incl_ora_total : OraTotal (Ora A incl_ora_mixin).
Proof. rewrite /OraTotal; eauto. Qed.

End incl.

#[global] Notation inclR A := (Ora A (incl_ora_mixin(A := A))).

(*Section functor.

Context (F : rFunctor) `{∀ A (CA : Cofe A) B (CB : Cofe B), CmraTotal (rFunctor_car F A B)}.

(* lift an rFunctor to the order *)
Program Definition inclRF : OrarFunctor := {|
  orarFunctor_car A _ B _ := inclR (rFunctor_car F A B);
  orarFunctor_map _ _ _ _ _ _ _ _ a := rFunctor_map F a;
|}.
Next Obligation.
  apply rFunctor_map_id.
Qed.
Next Obligation.
  apply rFunctor_map_compose.
Qed.
Next Obligation.
  split.
  - pose proof (rFunctor_mor F fg) as Hc.
    rewrite /ora_cmraR /ora_car /ora_equiv /ora_dist /ora_pcore /ora_op /ora_valid /ora_validN /ora_cmra_mixin.
    assert (Cmra' _ (cmra_ofe_mixin (@rFunctor_car F A1 Cofe0 B1 Cofe2)) (cmra_mixin (@rFunctor_car F A1 Cofe0 B1 Cofe2)) = rFunctor_car F A1 B1) as Hc1.
    { clear; destruct rFunctor_car; reflexivity. }
    unfold cmra_ofeO in *.
    admit.
  - by intros; apply cmra_morphism_monotoneN; first apply rFunctor_mor.
  - intros ??; apply @incl_increasing.
Admitted.

#[global] Instance inclRF_contractive `{rFunctorContractive F} : OrarFunctorContractive inclRF := _.

End functor.*)

Section flat.

(* This works, but only for very restricted algebras. *)

Context {A : ucmra} (core_unit : forall (a : A), core a ≡ ε) {discrete_unit : Discrete (ε : A)}.

Instance flat_orderN : OraOrderN A := dist.
Instance flat_order : OraOrder A := equiv.

Lemma Increasing_unit : forall (a : A), Increasing a <-> a ≡ ε.
Proof.
  split; intros Ha.
  - specialize (Ha ε).
    by rewrite right_id in Ha.
  - by intros ?; rewrite Ha left_id.
Qed.

Definition flat_ora_mixin : OraMixin A.
Proof.
  apply ora_total_mixin; try apply _; try done.
  - apply cmra_unit_cmra_total.
  - by intros ?; rewrite Increasing_unit.
  - intros ???; rewrite !Increasing_unit.
    by intros -> ?%discrete_iff.
  - apply cmra_core_ne.
  - intros ?????.
    rewrite /OraorderN /flat_orderN =>Hdist.
    symmetry in Hdist; apply cmra_extend in Hdist as (z & ? & Heq1 & Hz & ?); last done.
    eexists _, _; split; last done.
    by rewrite Heq1.
  - eauto.
  - apply dist_S.
  - by intros ???? ->.
  - by intros ???? ->.
  - apply equiv_dist.
  - intros ???.
    rewrite !cmra_pcore_core !core_unit.
    inversion 1; subst.
    eexists; split; last done.
    by constructor.
Qed.

Local Canonical Structure flatR : ora := Ora A flat_ora_mixin.
Local Canonical Structure flatUR : uora := Uora A (ucmra_mixin A).

End flat.

(*#[global] Notation flatR A := (Uora A (ucmra_mixin A)).*)
