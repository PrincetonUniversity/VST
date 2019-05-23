Require Import VST.floyd.base.
Require Import VST.floyd.canon.

Local Open Scope logic.

Definition wp {cs: compspecs} {Ora: OracleKind} (Delta: tycontext) (c: statement) (Q: ret_assert): environ -> mpred :=
  EX P: environ -> mpred, !! semax Delta P c Q && P.

Definition wp_spec: forall {cs: compspecs} {Ora: OracleKind} (Delta: tycontext) P c Q,
  P |-- wp Delta c Q <-> semax Delta P c Q.
Proof.
  intros.
  split; intros.
  + eapply semax_pre.
    - apply andp_left2, H.
    - unfold wp.
      apply semax_extract_exists.
      clear P H.
      intros P.
      apply semax_extract_prop.
      auto.
  + unfold wp.
    apply (exp_right P).
    apply andp_right.
    - apply prop_right; auto.
    - auto.
Qed.

Section wp_seq.

Parameter semax_seq_inv': forall {CS: compspecs} {Espec: OracleKind} Delta P R h t,
    @semax CS Espec Delta P (Ssequence h t) R ->
    @semax CS Espec Delta P h (overridePost (EX Q: environ -> mpred, !! (@semax CS Espec Delta Q t R) && Q) R).
(* line 478 in SeparationLogicAsLogic *)
Check semax_conseq.
Lemma wp_seq: forall {CS: compspecs} {Espec: OracleKind} Delta P c1 c2,
  wp Delta (Ssequence c1 c2) P = wp Delta c1 (overridePost (wp Delta c2 P) P).
Proof.
  intros.
  rename P into R.
  apply pred_ext.
  + unfold wp at 1.
    apply exp_left; intros P.
    apply derives_extract_prop.
    intros.
    unfold wp at 1.
    apply (exp_right P).
    apply andp_right; [apply prop_right | auto].
    apply semax_seq_inv' in H.
    exact H.
  + unfold wp at 1.
    apply exp_left; intros P.
    apply derives_extract_prop.
    intros.
    unfold wp at 1.
    apply (exp_right P).
    apply andp_right; [apply prop_right | auto].
    apply semax_seq with (wp Delta c2 R); auto.
    apply wp_spec.
    auto.
Qed.

End wp_seq.
