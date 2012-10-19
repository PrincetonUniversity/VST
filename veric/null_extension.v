Load loadpath.
Require Import msl.base
               veric.sim veric.step_lemmas veric.base veric.expr
               veric.extensions veric.extspec.

Set Implicit Arguments.

Section NullExtSpec.
Variables (M ext_state: Type) (ext_spec_type: AST.external_function -> Type).

Definition null_extspec := Build_external_specification 
  M AST.external_function ext_state
  ext_spec_type
  (fun (ef: AST.external_function) (_:ext_spec_type ef) 
       (tys: list typ) (args: list val) (z: ext_state) (m: M) => False)
  (fun (ef: AST.external_function) (_:ext_spec_type ef) 
       (ty: option typ) (ret: option val) (z: ext_state) (m: M) => True).

End NullExtSpec.

Section NullExtsig.
Variable (M ext_state: Type) (ext_spec_type: AST.external_function -> Type).

Definition null_extsig := mk_extsig nil (null_extspec M ext_state ext_spec_type).

End NullExtsig.

Section NullExtension.
Variables 
  (G C M D ext_state: Type) 
  (csem: CoreSemantics G C M D)
  (signature: extsig M ext_state)
  (init_world: ext_state)

  (after_at_external_excl: forall c ret c',
    after_external csem ret c = Some c' -> at_external csem c' = None)
  (at_external_handled: forall c ef args sig,
    at_external csem c = Some (ef, sig, args) -> handles ef signature).

Definition cores := fun _:nat => Some csem.

Definition extension_state := (ext_state*C)%type.

Program Definition wsem: CoreSemantics G extension_state M D := 
  Build_CoreSemantics G extension_state M D 
  (initial_mem csem)
  (fun ge f args => match make_initial_core csem ge f args with
                    | None => None
                    | Some c => Some (init_world, c)
                    end)
  (at_external csem oo snd)
  (fun ret s => match after_external csem ret (snd s) with 
                | None => None
                | Some c => Some (fst s, c)
                end)
  (fun ge s => safely_halted csem ge (snd s))
  (fun ge s m s' m' => corestep csem ge (snd s) m (snd s') m' /\ fst s=fst s')
  _ _ _.
Next Obligation.
destruct q; destruct q'; unfold compose; simpl in *.
eapply corestep_not_at_external; eauto.
Qed.
Next Obligation.
destruct q; destruct q'; simpl in *.
eapply corestep_not_halted; eauto.
Qed.
Next Obligation.
destruct q; unfold compose; simpl in *.
eapply at_external_halted_excl.
Qed.

Local Open Scope nat_scope.
 
Definition proj_core (s: extension_state) (i:nat) := 
  if eq_nat_dec i 1 then Some (snd s) else None.
Definition active := fun _:extension_state => 1.
Definition runnable := fun (ge: G) (s :extension_state) => 
  match at_external csem (snd s), safely_halted csem ge (snd s) with 
  | None, None => Some 1
  | _, _ => None
  end.
Definition proj_ext_state := @fst ext_state C.
Definition lift_pred (P: ext_state -> M -> Prop) := 
  fun p:extension_state => P (fst p).
Definition inj_ext_state (z: ext_state) (s: extension_state) := 
  (z, snd s).

(*Users will typically have to prove that their extension and client signatures
   are compatible; here, we assume it since we are parametric in signature*)
Variable null_extsig_linkable: forall S, 
  linkable proj_ext_state S (null_extsig M (ext_state*C) 
    (ext_spec_type signature)).

Local Hint Unfold cores proj_core active runnable proj_ext_state 
  lift_pred inj_ext_state : null_unfold.

Obligation Tactic := 
  autounfold with null_unfold;
  intros; try solve [eexists; eauto|congruence].

Program Definition null_extension := Extension.Make 
  wsem cores signature (null_extsig _ _ (ext_spec_type signature)) 
  proj_core _
  active _ _
  runnable _ _ _ _
  proj_ext_state lift_pred _ _ _
  inj_ext_state _ _.
Next Obligation.
revert H0; case_eq (eq_nat_dec i 1).
intros -> _; exists (snd w); auto.
congruence.
Qed.
Next Obligation.
if_tac; exists (snd w); auto.
elimtype False; apply H; auto.
Qed.
Next Obligation. 
destruct (at_external csem (snd w)); try solve[congruence]. 
destruct (safely_halted csem ge (snd w)); try solve[congruence].
Qed.
Next Obligation. 
case_eq (at_external csem (snd w)); try solve[congruence]. 
intros [ef args] H2.
rewrite H2 in H; right; exists ef; exists args.
inversion H0; subst; auto.
inversion H1; subst; auto.
intros H2; rewrite H2 in H.
case_eq (safely_halted csem ge (snd w)). 
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
Next Obligation. destruct w; destruct w'; simpl in *; destruct H; auto. Qed.
Next Obligation. apply null_extsig_linkable. Qed.

Section NullExtensionSafe.
Variable (csem_det: forall ge c m c' m' c'' m'',
           corestep csem ge c m c' m' -> corestep csem ge c m c'' m'' -> 
           (c', m')=(c'', m'')).

Lemma null_extension_safe : safe_extension null_extension.
Proof.
apply safety_criteria_safe; constructor; autounfold with null_unfold in *.

(*1*) intros until m'; intros H1 H2 [H3 H4] H5 H6. 
split; auto. split; auto. inversion H6; subst; simpl.
autounfold with null_unfold in *.
inversion H3; rewrite H7 in *.
inversion H4; rewrite H8 in *.
f_equal; generalize (csem_det _ _ _ _ _ _ _ H H5); inversion 1; auto.
inversion H6; subst.
unfold Extension.all_safe; intros i CS0 c0; inversion 1.
rewrite H8 in *.
intros H9; simpl in H4; autounfold with null_unfold in *; simpl in *.
autounfold with null_unfold in *.
inversion H4; rewrite H10 in *.
inversion H9; rewrite H11 in *.
if_tac in H11; try solve[congruence].
inversion H11; rewrite H13 in *.
eapply safe_corestep_forward; eauto.
unfold corestep_fun; intros; eapply csem_det; eauto.
specialize (H1 1 CS0 (snd w)); unfold proj_ext_state in H1.
rewrite <-H0.
assert (Extension.proj_ext_state null_extension w = fst w).
 simpl; autounfold with null_unfold; auto.
rewrite <-H10, <-H12; apply H1; auto.

(*2*) intros until CS; intros H1 H2 H3 [H4 H5].
spec H1 i CS c H4 H5.
simpl in H3.
destruct w.
unfold runnable in H3; simpl in H3.
case_eq (at_external csem c0).
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
exists c'; exists (e, c'); exists m'; split; auto.
rewrite <-H7; auto.
split; auto.
simpl.
split; auto.

(*3*) intros until x; intros [H1 H2] H3 H4 H5 H6 H7 H8.
simpl in H6; unfold lift_pred in H6.
generalize (Extension.csem_wsem_linkable null_extension); intros [H9 H10].
simpl in H10.
specialize (H10 ef x x).
specialize (H10 (ext_spec_pre (null_extsig M extension_state 
  (ext_spec_type signature)) ef x)).
specialize (H10 (ext_spec_post (null_extsig M extension_state
  (ext_spec_type signature)) ef x)).
specialize (H10 P Q).
spec H10; auto.
spec H10; auto.
destruct H10 as [H10 H11].
specialize (H10 (sig_args sig) args w m H6); elimtype False; auto.

(*4*) intros until m; intros H1 H2 H3.
simpl in H2; unfold runnable in H2.
inversion H3; subst.
unfold compose in H0;  simpl in H0.
rewrite H0 in H2.
case_eq (safely_halted csem ge (snd w)); intros; try solve[congruence].
rewrite H in H2.
right; exists i; auto.
rewrite H in H2; congruence.

(*5*) intros until rv; intros [H1 H2] H3 H4.
split; auto.
simpl.
inversion H4; subst.
apply corestep_not_halted in H.
simpl in H2; inversion H2; subst.
inversion H1; rewrite H7 in *.
unfold proj_core in H6.
if_tac in H6; try solve[congruence].

(*6*) intros until CS; inversion 1; subst.
intros H4 H5; intros until j; intros H6; split.
intros [H7 H8]. 
split; auto.
simpl in H8; unfold proj_core in H8; simpl in H8; inversion H8; subst.
simpl; unfold proj_core; simpl.
simpl in H6; unfold active in H6.
if_tac; auto; exfalso; apply H6; auto.
intros n [H7 H8].
simpl in H8; unfold proj_core in H8; simpl in H8.
simpl in H6; unfold active in H6; simpl in H6.
if_tac in H8; auto.
inversion H8; subst.
exfalso; apply H6; auto.
congruence.

(*7*) intros until args; intros H1.
exists csem; exists (snd w); split; auto.

(*8*) intros until x.
intros [H1 H2] H3 H4 H5 H6.
generalize (Extension.csem_wsem_linkable null_extension); intros [_ H10].
specialize (H10 ef x x).
specialize (H10 (ext_spec_pre (null_extsig M extension_state 
  (ext_spec_type signature)) ef x)).
specialize (H10 (ext_spec_post (null_extsig M extension_state
  (ext_spec_type signature)) ef x)).
specialize (H10 P Q).
spec H10; auto.
spec H10; auto.
destruct H10 as [H10 H11].
specialize (H10 tys args w m H4); elimtype False; auto.

(*9*) intros until x; intros [H1 H2] H3 H4 H5 H6 H7 [H8 H9]; 
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

End NullExtensionSafe.

End NullExtension.