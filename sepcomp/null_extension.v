Require Import sepcomp.core_semantics.
Require Import sepcomp.forward_simulations.
Require Import sepcomp.rg_semantics.
Require Import sepcomp.rg_forward_simulations.
Require Import sepcomp.step_lemmas.
Require Import sepcomp.extspec.
Require Import sepcomp.extension.
Require Import sepcomp.extension_safety.
Require Import sepcomp.extension_simulations.
Require Import sepcomp.extension_proof_safety.
Require Import sepcomp.extension_proof.
Require Import sepcomp.Coqlib2. 

Require Import Axioms.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import compcert.common.Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Coqlib.

Set Implicit Arguments.

Section NullExtension.
 Variables
  (fT vT cT (*dT*) Z: Type) (** external states *)
  (csemT: CoreSemantics (Genv.t fT vT) cT mem (*dT*)) 
  (csig: ef_ext_spec mem Z) (** client signature *)
  (genv_mapT: forall i:nat, Genv.t fT vT).

 Definition cores := fun _:nat => csemT.

 Local Open Scope nat_scope.

 Definition xT := cT.
 Definition proj_core (i: nat) (s: xT) := if eq_nat_dec i 0 then Some s else None.
 Definition active := fun _:xT => 0.
 Definition runnable := fun (s: xT) => 
   match at_external csemT s, halted csemT s with 
     | None, None => true
     | _, _ => false
   end.
 Definition proj_zint := fun _:xT => tt.
 Definition proj_zext := fun z: Z => z.
 Definition zmult := fun (_:unit) (z: Z) => z.
 Definition handled: list AST.external_function := nil.

 Local Hint Unfold cores proj_core active runnable proj_zint : null_unfold.
 Obligation Tactic := autounfold with null_unfold; 
  intros; try solve [eexists; eauto|congruence].

 Program Definition null_extension := @Extension.Make 
  (*_*) _ _ _ _ _ _ 
  csemT csig (fun _ => Genv.t fT vT) (*(fun _ => dT)*) _ (fun _ => csemT) 
  csig (const 1) proj_core _ active _ proj_zint proj_zext zmult _ _ _ _.
 Next Obligation. if_tac; auto. rewrite H0 in H. unfold const in *. elimtype False; omega. Qed.
 Next Obligation. if_tac; exists s; auto. elimtype False; apply H; auto. Qed.
 Next Obligation. 
  split; auto.
  if_tac. 
  2: solve[elimtype False; apply H; omega].
  unfold linkable.
  intros.
  unfold proj_zext.
  rewrite H1 in H2; inv H2.
  solve[exists x'; split; auto].
 Qed.
 Next Obligation. if_tac in H; try solve[congruence]. Qed.

End NullExtension.

Section NullExtensionSafe.
 Variables
  (fT vT cT (*dT*) Z: Type) (** external states *)
  (csemT: CoreSemantics (Genv.t fT vT) cT mem (*dT*)) 
  (csig: ef_ext_spec mem Z) (** client signature *)
  (genv_mapT: forall i:nat, Genv.t fT vT)
  (ge: Genv.t fT vT).

 Import ExtensionSafety.

 Local Hint Unfold cores proj_core active runnable proj_zint : null_unfold.

 Obligation Tactic := autounfold with null_unfold;
  intros; try solve [eexists; eauto|congruence].

 Lemma null_extension_safe (csem_fun: corestep_fun csemT): 
  safe_extension ge (fun _:nat => ge) (null_extension csemT csig).
 Proof.
 destruct (ExtensionSafety ge (fun _:nat => ge) (null_extension csemT csig)) as [PF].
 apply PF.
 constructor; autounfold with null_unfold in *.

 (*1*) intros until m'; intros H1 H4 H5 H6. 
 assert (H3:True) by auto.
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
 intros until c0; intros H0.
 assert (H8:True) by auto.
 inversion H0 as [H7]. simpl in H0. rewrite H7 in *; clear H0.
 unfold proj_core in H7.
 if_tac in H7; try solve[congruence].
 rewrite <-H0 in *; clear H; inversion H7 as [H].
 rewrite H in *; clear H7 H.
 solve[eapply safe_corestep_forward; eauto].

 (*2*) intros until c; intros H1 H3 H5.
 assert (H4:True) by auto.
 specialize (H1 (active s) c H3).
 simpl in H3; unfold rg_forward_simulations.runnable, runnable in H5; simpl in H5.
 case_eq (at_external csemT s).
 intros [[ef sig] args] H6.
 unfold proj_core in H3; if_tac in H3; try congruence. inv H3.
 unfold const in *; rewrite H6 in H5.
 congruence.
 unfold proj_core in H3; if_tac in H3; try congruence. inv H3.
 intros H6; unfold const in *; rewrite H6 in H5.
 case_eq (halted csemT c); try congruence.
 intros rv Hsafe; rewrite Hsafe in H5.
 congruence.
 simpl in H1; rewrite H6 in H1.
 intros Hsafe; rewrite Hsafe in H1.
 destruct H1 as [c' [m' [H1 H7]]].
 solve[exists c'; exists c'; exists m'; split; auto].

 (*3*) intros until x; intros H2 H3 H4 H5 H6 H7 H8.
 assert (H1:True) by auto.
 unfold Extension.handled in H4.
 specialize (H4 s c sig args).
 spec H4; auto.
 spec H4; auto.
 solve[simpl in H2; inv H2; rewrite H3 in H4; congruence].

 (*4*) intros until c; intros H1 H2 H3.
 simpl in H3; unfold rg_forward_simulations.runnable, runnable in H3.
 simpl in H2; unfold proj_core in H2; if_tac in H2; try congruence. inv H2.
 intros H4; unfold const in *; rewrite H4 in H3.
 case_eq (halted csemT c); intros; try solve[congruence].
 rewrite H0 in H3.
 right; exists v; auto.
 solve[rewrite H0 in H3; congruence].

 (*5*) intros until rv; intros H2 H3 H4.
 unfold const in *.
 simpl.
 apply corestep_not_halted in H4.
 simpl in H2; inversion H2; subst.
 unfold proj_core in H0.
 solve[if_tac in H0; try solve[congruence]].

 (*6*) intros until c; inversion 1; subst.
 intros H4 H5; intros until c0; intros H6; split.
 intros H8.
 assert (H7:True) by auto.
 simpl in H8; unfold proj_core in H8; simpl in H8; inversion H8; subst.
 simpl; unfold proj_core; simpl.
 simpl in H6; unfold active in H6.
 if_tac; auto.
 exfalso; apply H6; auto.
 intros n z z' H8.
 assert (H7:True) by auto.
 simpl in H8; unfold proj_core in H8; simpl in H8.
 simpl in H6; unfold active in H6; simpl in H6.
 if_tac in H8; auto.
 inversion H8; subst.
 exfalso; apply H6; auto.
 solve[congruence].

 (*7*) intros until args; intros H1.
 solve[exists s; split; auto].

 (*8*) intros until Q.
 unfold const in *.
 intros H2 H3 H4 H5 H6.
 assert (H1:True) by auto.
 intros H12; simpl; exists c'; split3; auto.
 simpl in H2; unfold proj_core in H2.
 if_tac in H2; try solve[congruence].

 (*9*) intros until Q; intros H2 H3 H4 H5 H6 H7 H70 [H8 H9]; 
 intros until c0; intros H10; split.
 intros H12.
 assert (H11:True) by auto.
 simpl in H12; unfold proj_core in H12; simpl in H12.
 if_tac in H12; auto.
 simpl in H9; unfold proj_core in H9; simpl in H9.
 simpl in H10; unfold active in H10; simpl in H10.
 exfalso; apply H10; auto.
 congruence.
 intros ge'  n H12.
 simpl in H10, H12.
 unfold active in H10; unfold proj_core in H12.
 if_tac in H12.
 exfalso; auto.
 congruence.
 Qed.

End NullExtensionSafe.

 Lemma null_core_compatible: forall F V C (*D*) Z (ge: Genv.t F V) 
         (csem: CoreSemantics (Genv.t F V) C mem (*D*)) (csig: ef_ext_spec mem Z)
         (csem_fun: corestep_fun csem),
   core_compatible ge (fun _:nat => ge) (null_extension csem csig).
 Proof.
 intros until csig.
 intros CSEM_FUN.
 constructor; simpl; auto.
 intros until c; intros H1 H2 H3.
 exists s'.
 simpl; unfold cores, active; simpl; split; auto.
 simpl in H2.
 solve[inv H2; auto].
 
 intros until m'; intros H1 H2 H3.
 unfold active, cores in *.
 split; auto.
 unfold proj_core; auto.
 if_tac; auto.
 unfold proj_core in H1.
 if_tac in H1; try congruence.
 inv H1.
 generalize (CSEM_FUN _ _ _ _ _ _ _ H2 H3).
 inversion 1; subst; auto.
 solve[elimtype False; auto].

 intros until m'; intros H1 H2.
 exists c'.
 unfold cores, active in H2.
 unfold proj_core in H1.
 solve[if_tac in H1; try congruence].

 intros until m'; intros H1 H2 H3; intros j; intros q H4.
 unfold cores, active in *.
 unfold proj_core.
 if_tac; auto.
 solve[elimtype False; omega].

 intros until n; intros H1 H2 H3 j H4.
 unfold active, cores in *.
 unfold proj_core.
 if_tac; auto.
 solve[elimtype False; auto].

 intros until retv; intros H1 H2.
 exists c'.
 unfold cores, active in H1, H2.
 inv H1.
 solve[split; auto].

 intros s s' retv H1 j H2.
 unfold proj_core; auto.
 unfold active in H2.
 if_tac; auto.
 solve[elimtype False; auto].

 intros until args; intros H1.
 exists s.
 unfold active, cores, proj_core.
 solve[split; auto].
 Qed.

 Lemma null_private_conserving: forall F V C (*D*) Z
         (csem: RelyGuaranteeSemantics (Genv.t F V) C (*D*)) (csig: ef_ext_spec mem Z),
   private_conserving _ (const csem) (null_extension csem csig).
 Proof.
 intros.
 unfold private_conserving.
 intros.
 simpl in *.
 unfold proj_core in H.
 if_tac in H; try solve[congruence].
 inv H.
 unfold const in H0.
 auto.
 Qed.

Section NullExtensionCompilable.
 Variables 
  (fS vS fT vT cS cT (*dS dT*) Z: Type) 
  (csig: ef_ext_spec mem Z)
  (init_world: Z)
  (entry_points: list (val*val*signature))
  (csemS: RelyGuaranteeSemantics (Genv.t fS vS) cS (*dS*))
  (csemT: RelyGuaranteeSemantics (Genv.t fT vT) cT (*dT*)).

 Variables (geS: Genv.t fS vS) (geT: Genv.t fT vT).

 Definition E_S: @Extension.Sig mem Z unit Z (Genv.t fS vS) (*dS*) cS csemS csig 
   _ (*_*) (const cS) (const csemS) csig :=
  null_extension csemS csig.
 Definition E_T: @Extension.Sig mem Z unit Z (Genv.t fT vT) (*dT*) cT csemT csig 
   _ (*_*) (const cT) (const csemT) csig :=
  null_extension csemT csig.

 Import RGForward_simulation_inj_exposed.
 Import ExtensionCompilability2.

 Variable core_data: Type.
 Variable match_state: core_data -> meminj -> cS -> mem -> cT -> mem -> Prop. 
 Variable core_ord: core_data -> core_data -> Prop.
 Variable core_simulation: RGForward_simulation_inject (*dS dT*) csemS csemT 
   geS geT entry_points core_data match_state core_ord.
 Variable core_simulationsRG: forall i:nat, 
   StableRelyGuaranteeSimulation.Sig csemS csemT geS match_state.
 Variable threads_max: nat.
 Variable threads_max_nonzero: (O < threads_max)%nat. (*Required by defn. of core_ords*)

 Variable match_state_runnable: 
  forall cd j s1 m1 s2 m2,
  match_state cd j s1 m1 s2 m2 -> 
  rg_forward_simulations.runnable csemS s1=rg_forward_simulations.runnable csemT s2.

 Lemma null_extension_compilable: 
   corestep_fun csemS -> corestep_fun csemT -> genvs_domain_eq geS geT -> 
   CompilableExtension.Sig csemS csemT geS geT entry_points.
 Proof.
 (*SOLVED BY econstructor; eauto.  WE'LL USE THE PROVIDED LEMMAS INSTEAD.*)
 intros H1 H2 H3.
 set (R := fun (_:meminj) (_:cS) (_:mem) (_:cT) (_:mem) => True).
 destruct (@ExtensionCompilability
   (*_ _ _ _ *)_ _ _ _ _ _ _ _ _ _ _ _ _
   csemS csemT csemS csemT csig csig 
   geS geT geS geT E_S E_T entry_points core_data match_state core_ord threads_max R)
  as [LEM].
 apply LEM; auto.
 solve[intros i; unfold const; apply genvs_domain_eq_refl; auto].
 solve[intros i; unfold const; apply genvs_domain_eq_refl; auto].
 unfold E_S, const.
 solve[apply (null_core_compatible geS csig H1)].
 unfold E_T, const.
 solve[apply (null_core_compatible geT csig H2)].
 solve[apply null_private_conserving].
 solve[apply null_private_conserving].

 constructor; try solve[intros; unfold R; auto].

 intros until j; intros H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15.
 inversion H4; subst.
 inversion H5; subst.
 apply corestep_not_at_external in H15.
 unfold const in H8; simpl in H8.
 rewrite H15 in H8.
 congruence.

 intros until j; intros.
 inversion H0; subst.
 inversion H4; subst.
 destruct core_simulation.
 solve[eapply core_at_external0 in H6; eauto].
 
 intros; destruct core_simulation.
 destruct (core_initial0 v1 v2 sig H vals1 s1 m1 j vals2 m2 H0 H4 H5 H6) 
  as [cd [s2 [H7 H8]]].
 exists (fun _ => cd); exists s2; split; auto. 
 split; auto.

 intros i c PROJ b PRIV.
 unfold const in PRIV.
 elimtype False.
 simpl in PROJ.
 unfold proj_core in PROJ.
 if_tac in PROJ; try solve[congruence].
 inv PROJ.
 solve[eapply (private_initial _ b geS v1 vals1 c); eauto].

 split.
 intros i k c d NEQ; simpl; intros PROJ1 PROJ2 b PRIV CONTRA.
 unfold proj_core in *.
 if_tac in PROJ1; try solve[congruence]; inv PROJ1.
 solve[if_tac in PROJ2; try solve[congruence]; inv PROJ2].

 split.
 intros i c PROJ b PRIV.
 unfold const in PRIV.
 elimtype False.
 simpl in PROJ.
 unfold proj_core in PROJ.
 if_tac in PROJ; try solve[congruence].
 inv PROJ.
 solve[eapply (private_initial _ b geT v2 vals2 c); eauto].

 split.
 intros i k c d NEQ; simpl; intros PROJ1 PROJ2 b PRIV CONTRA.
 unfold proj_core in *.
 if_tac in PROJ1; try solve[congruence]; inv PROJ1.
 solve[if_tac in PROJ2; try solve[congruence]; inv PROJ2].

 split.
 solve[unfold R; auto].
 split; auto.
 intros i c1 H9; exists s2; split; auto.
 simpl in H9; unfold proj_core in H9|-*; if_tac in H9; try congruence.
 simpl; unfold proj_core; rewrite H10; if_tac; auto.
 solve[elimtype False; auto].
 simpl in H9; unfold proj_core in H9.
 if_tac in H9; try congruence.
 solve[unfold const; inversion H9; rewrite H12 in *; auto].

 intros until v1; intros ty MATCH12 HALT HASTY.
 unfold CompilabilityInvariant.match_states, const in MATCH12.
 destruct MATCH12 as [? [? [? [? [? [? MATCH12]]]]]].
 specialize (MATCH12 O c1).
 spec MATCH12; auto.
 destruct MATCH12 as [c2' [PROJ MATCH12]].
 simpl in PROJ; unfold proj_core in PROJ; inv PROJ.
 destruct core_simulation.
 solve[eapply core_halted0 in HALT; eauto].

 intros; destruct core_simulation.
 apply corestep_not_halted in H6.
 simpl in H0; unfold proj_core, active in H0.
 if_tac in H0; try congruence.
 inversion H0; rewrite H9 in *. 
 solve[simpl in H5; unfold const in H5; rewrite H5 in H6; congruence].
 Qed.

End NullExtensionCompilable.
