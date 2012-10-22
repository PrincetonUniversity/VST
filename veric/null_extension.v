Load loadpath.
Require Import msl.base
               veric.sim veric.step_lemmas veric.base veric.expr
               veric.extensions veric.extspec.

Set Implicit Arguments.

Section NullExtSpec.
Variables (M Z: Type) (ext_spec_type: AST.external_function -> Type).

Definition null_extspec := Build_external_specification 
  M AST.external_function Z
  ext_spec_type
  (fun (ef: AST.external_function) (_:ext_spec_type ef) 
       (tys: list typ) (args: list val) (z: Z) (m: M) => False)
  (fun (ef: AST.external_function) (_:ext_spec_type ef) 
       (ty: option typ) (ret: option val) (z: Z) (m: M) => True).

End NullExtSpec.

Section NullExtsig.
Variable (M Z: Type) (ext_spec_type: AST.external_function -> Type).

Definition null_extsig := mkextsig nil (null_extspec M Z ext_spec_type).

End NullExtsig.

Section NullExtension.
Variables 
  (G cT M D Z: Type) 
  (csem: CoreSemantics G cT M D)
  (client_sig: ext_sig M Z)
  (init_world: Z)

  (after_at_external_excl: forall c ret c',
    after_external csem ret c = Some c' -> at_external csem c' = None)
  (at_external_handled: forall c ef args sig,
    at_external csem c = Some (ef, sig, args) -> IN ef client_sig = true).

Definition cores := fun _:nat => Some csem.

Local Open Scope nat_scope.

Definition proj_core (c: cT) (i: nat) := if eq_nat_dec i 1 then Some c else None.
Definition active := fun _: cT => 1.
Definition runnable := fun (ge: G) (s: cT) => 
  match at_external csem s, safely_halted csem ge s with 
  | None, None => Some 1
  | _, _ => None
  end.
Definition proj_zint := fun _: cT => tt.
Definition proj_zext := fun z: Z => z.
Definition zmult := fun (_: unit) (z: Z) => z.
Definition handled: list AST.external_function := nil.

Local Hint Unfold cores proj_core active runnable proj_zint : null_unfold.

Obligation Tactic := 
  autounfold with null_unfold;
  intros; try solve [eexists; eauto|congruence].

Program Definition null_extension := Extension.Make 
  csem cores client_sig client_sig handled
  proj_core _
  active _ _
  runnable _ _ _ _ _ _
  proj_zint proj_zext zmult _ _ _.
Next Obligation.
revert H0; case_eq (eq_nat_dec i 1).
intros -> _; exists s; auto.
congruence.
Qed.
Next Obligation.
if_tac; exists s; auto.
elimtype False; apply H; auto.
Qed.
Next Obligation. 
destruct (at_external csem s); try solve[congruence]. 
destruct (safely_halted csem ge s); try solve[congruence].
Qed.
Next Obligation. 
case_eq (at_external csem s); try solve[congruence]. 
intros [ef args] H2.
rewrite H2 in H; right; exists ef; exists args.
inversion H0; subst; auto.
inversion H1; subst; auto.
intros H2; rewrite H2 in H.
case_eq (safely_halted csem ge s). 
intros rv H3; left; exists rv.
inversion H0; subst.
inversion H1; subst.
auto.
intros H3.
rewrite H3 in H.
congruence.
Qed.
Next Obligation. inversion H; subst; eapply after_at_external_excl; eauto. Qed.
Next Obligation. inversion H; subst; eapply at_external_handled; eauto. Qed.
Next Obligation. inversion H; subst; if_tac in H0; try congruence. Qed.
Next Obligation. unfold linkable; intros; inv H0; inv H1; exists x'; auto. Qed.

Lemma null_extension_safe (csem_fun: corestep_fun csem) : 
  safe_extension null_extension.
Proof.
apply safety_criteria_safe; constructor; autounfold with null_unfold in *.

(*1*) intros until m'; intros H1 H2 [H3 H4] H5 H6. 
inversion H3 as [H7]; rewrite <-H7 in *; clear H7 H3.
unfold Extension.proj_core in H4; simpl in H4.
generalize H4 as H4'; intro.
unfold proj_core in H4; if_tac in H4; try solve[congruence].
inversion H4 as [H7]; rewrite H7 in *; clear H7 H4.
rewrite H in *; clear H.
split; auto.
split; auto.
unfold Extension.proj_core; simpl; unfold proj_core.
if_tac; try solve[congruence].
f_equal; generalize (csem_fun _ _ _ _ _ _ _ H5 H6); inversion 1; auto.
simpl in H1|-*.
unfold proj_zint, Extension.all_safe in *.
intros until c0; intros H H8.
inversion H as [H7]; rewrite H7 in *; clear H.
unfold Extension.proj_core in H8; simpl in H8; unfold proj_core in H8.
if_tac in H8; try solve[congruence].
rewrite <-H in *; clear H; inversion H8 as [H].
rewrite H in *; clear H8 H.
eapply safe_corestep_forward; eauto.

(*2*) intros until CS; intros H1 H2 H3 [H4 H5].
spec H1 i CS c H4 H5.
simpl in H3.
unfold runnable in H3; simpl in H3.
case_eq (at_external csem s).
intros [ef args] H6.
rewrite H6 in H3.
simpl in H5; unfold proj_core in H5; simpl in H5; inversion H5; subst.
congruence.
intros H6.
rewrite H6 in H3.
inversion H3; subst.
simpl in H1.
inversion H6; subst.
simpl in H5; unfold proj_core in H5; simpl in H5; inversion H5; subst.
inversion H4; rewrite H7 in *.
rewrite H2 in H1.
rewrite <-H7 in H1.
destruct (safely_halted csem ge c); try solve[congruence].
destruct H1 as [c' [m' [H8 H9]]].
exists c'; exists c'; exists m'; split; auto.
rewrite <-H7; auto.

(*3*) intros until x; intros [H1 H2] H3 H4 H5 H6 H7 H8.
apply ListSet.set_mem_correct1 in H4.
unfold handled, ListSet.set_In in H4.
inversion H4.

(*4*) intros until m; intros H1 H2 H3.
simpl in H2; unfold runnable in H2.
inversion H3; subst.
unfold compose in H0;  simpl in H0.
rewrite H0 in H2.
case_eq (safely_halted csem ge s); intros; try solve[congruence].
rewrite H in H2.
right; exists i; auto.
rewrite H in H2; congruence.

(*5*) intros until rv; intros [H1 H2] H3 H4.
split; auto.
simpl.
apply corestep_not_halted in H4.
simpl in H2; inversion H2; subst.
inversion H1; rewrite H5 in *.
unfold proj_core in H0.
if_tac in H0; try solve[congruence].

(*6*) intros until CS; inversion 1; subst.
intros H4 H5; intros until j; intros H6; split.
intros [H7 H8]. 
split; auto.
simpl in H8; unfold proj_core in H8; simpl in H8; inversion H8; subst.
simpl; unfold proj_core; simpl.
simpl in H6; unfold active in H6.
if_tac; auto; exfalso; apply H6; auto.
intros n z z' [H7 H8].
simpl in H8; unfold proj_core in H8; simpl in H8.
simpl in H6; unfold active in H6; simpl in H6.
if_tac in H8; auto.
inversion H8; subst.
exfalso; apply H6; auto.
congruence.

(*7*) intros until args; intros H1.
exists csem; exists s; split; auto.

(*8*) intros until Q.
intros [H1 H2] H3 H4 H5 H6.
intros H12; simpl; exists c'; split3; auto.
simpl in H2; unfold proj_core in H2.
if_tac in H2; try solve[congruence].

(*9*) intros until Q; intros [H1 H2] H3 H4 H5 H6 H7 [H8 H9]; 
 intros until j; intros H10; split.
intros [H11 H12].
simpl in H12; unfold proj_core in H12; simpl in H12.
if_tac in H12; auto.
simpl in H9; unfold proj_core in H9; simpl in H9.
simpl in H10; unfold active in H10; simpl in H10.
exfalso; apply H10; auto.
congruence.
intros ge n [H11 H12].
simpl in H10, H12.
unfold active in H10; unfold proj_core in H12.
if_tac in H12.
rewrite H in H10; exfalso; auto.
congruence.
Qed.

End NullExtension.
