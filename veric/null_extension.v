Load loadpath.
Require Import msl.base
               veric.sim veric.step_lemmas veric.base veric.expr veric.extspec
               veric.extension veric.extension_proof.

Set Implicit Arguments.

Section NullExtension.
 Variables 
  (F V cT D Z: Type) 
  (ge: Genv.t F V)
  (csem: CoreSemantics (Genv.t F V) cT mem D)
  (csig: ext_sig mem Z)
  (init_world: Z)
  (at_external_handled: forall c ef args sig,
    at_external csem c = Some (ef, sig, args) -> IN ef csig = true).

Definition cores := fun _:nat => Some csem.

Local Open Scope nat_scope.

Definition proj_core (i: nat) (c: cT) := if eq_nat_dec i 1 then Some c else None.
Definition active := fun _: cT => 1.
Definition runnable := fun (s: cT) => 
  match at_external csem s, safely_halted csem s with 
  | None, None => true
  | _, _ => false
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
  _
  csem cores csig csig handled
  proj_core _  
  active _ _
  runnable _ _ _ _  
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
if_tac in H1; try congruence; inv H1; inv H0.
destruct (at_external CS c); try solve[congruence].
destruct p as [[? ?] ?]. 
right; eexists; eexists; eexists; eauto.
destruct (safely_halted CS c); try solve[congruence].
left; eexists; eauto.
Qed.
Next Obligation. inversion H; subst; eapply at_external_handled; eauto. Qed.
Next Obligation. inversion H; subst; if_tac in H0; try congruence. Qed.
Next Obligation. unfold linkable; intros; inv H0; inv H1; exists x'; auto. Qed.

End NullExtension.

Section NullExtensionSafe.
 Variables 
  (F V cT D Z: Type) 
  (ge: Genv.t F V)
  (csem: CoreSemantics (Genv.t F V) cT mem D)
  (csig: ext_sig mem Z)
  (init_world: Z)
  (at_external_handled: forall c ef args sig,
    at_external csem c = Some (ef, sig, args) -> IN ef csig = true).

Import ExtensionSafety.

Local Hint Unfold cores proj_core active runnable proj_zint : null_unfold.

Obligation Tactic := 
  autounfold with null_unfold;
  intros; try solve [eexists; eauto|congruence].

Lemma null_extension_safe (csem_fun: corestep_fun csem): 
 safe_extension ge (fun _:nat => ge) (null_extension csem csig at_external_handled).
Proof.
destruct (ExtensionSafety (null_extension csem csig at_external_handled) 
  ge (fun _:nat => ge)) as [PF].
apply PF.
constructor; autounfold with null_unfold in *.

(*1*) intros until m'; intros H1 [H3 H4] H5 H6. 
inversion H3 as [H7]; rewrite <-H7 in *; clear H7 H3.
unfold Extension.proj_core in H4; simpl in H4.
generalize H4 as H4'; intro.
unfold proj_core in H4; if_tac in H4; try solve[congruence].
inversion H4 as [H7]; rewrite H7 in *; clear H7 H4.
rewrite H in *; clear H.
unfold Extension.proj_core; simpl; unfold proj_core.
simpl in H5.
f_equal; generalize (csem_fun _ _ _ _ _ _ _ H5 H6); inversion 1; auto.
simpl in H1|-*.
unfold proj_zint, all_safe in *.
intros until c0; intros H0 H8.
inversion H0 as [H7]; rewrite H7 in *; clear H0.
unfold Extension.proj_core in H8; simpl in H8; unfold proj_core in H8.
if_tac in H8; try solve[congruence].
rewrite <-H0 in *; clear H; inversion H8 as [H].
rewrite H in *; clear H8 H.
solve[eapply safe_corestep_forward; eauto].

(*2*) intros until CS; intros H1 H3 [H4 H5].
spec H1 (active s) CS c H4 H5.
simpl in H5.
simpl in H3; unfold runnable in H3; simpl in H3.
case_eq (at_external csem s).
intros [[ef sig] args] H6.
rewrite H6 in H3.
simpl in H5; unfold proj_core in H5; simpl in H5; inversion H5; subst.
congruence.
intros H6.
rewrite H6 in H3.
unfold proj_core in H5.
if_tac in H5; try congruence.
inv H5.
case_eq (safely_halted csem c); try congruence.
intros rv Hsafe.
rewrite Hsafe in H3.
congruence.
simpl in H1.
inversion H4.
rewrite <-H2 in *.
rewrite H6 in H1.
intros Hsafe; rewrite Hsafe in H1.
destruct H1 as [c' [m' [H1 H7]]].
solve[exists c'; exists c'; exists m'; split; auto].

(*3*) intros until x; intros [H1 H2] H3 H4 H5 H6 H7 H8.
apply ListSet.set_mem_correct1 in H4.
unfold handled, ListSet.set_In in H4.
solve[inversion H4].

(*4*) intros until m; intros H1 H2 H3.
simpl in H2; unfold runnable in H2.
inversion H3; subst.
unfold compose in H0;  simpl in H0.
rewrite H0 in H2.
case_eq (safely_halted csem s); intros; try solve[congruence].
rewrite H in H2.
right; exists v; auto.
solve[rewrite H in H2; congruence].

(*5*) intros until rv; intros [H1 H2] H3 H4.
split; auto.
simpl.
apply corestep_not_halted in H4.
simpl in H2; inversion H2; subst.
inversion H1; rewrite H5 in *.
unfold proj_core in H0.
solve[if_tac in H0; try solve[congruence]].

(*6*) intros until CS; inversion 1; subst.
intros H4 H5; intros until j; intros H6; split.
intros [H7 H8]. 
split; auto.
simpl in H8; unfold proj_core in H8; simpl in H8; inversion H8; subst.
simpl; unfold proj_core; simpl.
simpl in H6; unfold active in H6.
if_tac; auto.
exfalso; apply H3; auto.
intros n z z' [H7 H8].
simpl in H8; unfold proj_core in H8; simpl in H8.
simpl in H6; unfold active in H6; simpl in H6.
if_tac in H8; auto.
inversion H8; subst.
exfalso; apply H3; auto.
solve[congruence].

(*7*) exists csem; exists s; split; auto. 

(*8*) intros until Q.
intros [H1 H2] H3 H4 H5 H6.
intros H12; simpl; exists c'; split3; auto.
simpl in H2; unfold proj_core in H2.
if_tac in H2; try solve[congruence].

(*9*) intros until Q; intros [H1 H2] H3 H4 H5 H6 H7 H70 [H8 H9]; 
 intros until j; intros H10; split.
intros [H11 H12].
simpl in H12; unfold proj_core in H12; simpl in H12.
if_tac in H12; auto.
simpl in H9; unfold proj_core in H9; simpl in H9.
simpl in H10; unfold active in H10; simpl in H10.
exfalso; apply H; auto.
congruence.
intros ge'  n [H11 H12].
simpl in H10, H12.
unfold active in H10; unfold proj_core in H12.
if_tac in H12.
exfalso; auto.
congruence.
Qed.

End NullExtensionSafe.

Section NullExtensionCompilable.
 Variables 
  (F_S V_S cS dS F_T V_T cT dT Z: Type) 
  (csemS: CoreSemantics (Genv.t F_S V_S) cS mem dS)
  (csemT: CoreSemantics (Genv.t F_T V_T) cT mem dT)
  (csig: ext_sig mem Z)
  (init_world: Z)
  (at_external_handledS: forall c ef args sig,
    at_external csemS c = Some (ef, sig, args) -> IN ef csig = true)
  (at_external_handledT: forall c ef args sig,
    at_external csemT c = Some (ef, sig, args) -> IN ef csig = true).

End NullExtensionCompilable.
