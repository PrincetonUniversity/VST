Require Import sepcomp.core_semantics.
Require Import sepcomp.core_semantics_lemmas.
Require Import sepcomp.forward_simulations.
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
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Coqlib.

Set Implicit Arguments.

Section NullExtension.
 Variables
  (fT vT cT dT Z: Type) (** external states *)
  (csemT: CoreSemantics (Genv.t fT vT) cT mem dT) 
  (csig: ef_ext_spec mem Z) (** client signature *)
  (genv_mapT: forall i:nat, Genv.t fT vT).

 Definition cores := fun _:nat => csemT.

 Local Open Scope nat_scope.

 Definition xT := cT.
 Definition proj_core (i u: nat) (s: xT) := 
   if eq_nat_dec i 0 then 
     if eq_nat_dec u 0 then Some s else None
   else None.
 Definition active := fun _:xT => 0.
 Definition runnable := fun (s: xT) => 
   match at_external csemT s, safely_halted csemT s with 
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
  _ _ _ _ _ _ _ 
  csemT csig (fun _ => Genv.t fT vT) (fun _ => dT) _ (fun _ => csemT) 
  csig (const 1) proj_core _ active _ proj_zint proj_zext zmult _ _ _ _ _.
 Next Obligation. if_tac; auto. rewrite H0 in H. unfold const in *. elimtype False; omega. Qed.
 Next Obligation. if_tac; exists 0; exists s; auto. elimtype False; apply H; auto. Qed.
 Next Obligation. 
  if_tac in H; subst; try solve[congruence].
  if_tac in H; subst; try solve[congruence].
  if_tac in H0; subst; try solve[congruence].
 Qed.
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
 Next Obligation.
  if_tac in H; try solve[congruence].
  if_tac in H; try solve[congruence].
 Qed.

End NullExtension.

Lemma null_core_compatible: forall F V C D Z (ge: Genv.t F V) 
         (csem: CoreSemantics (Genv.t F V) C mem D) (csig: ef_ext_spec mem Z)
         (csem_fun: corestep_fun csem),
   core_compatible ge (fun _:nat => ge) (null_extension csem csig).
Proof.
  intros until csig.
  intros CSEM_FUN.
  constructor; simpl; auto.
  intros until c; intros H1 H2 H3.
  exists s'.
  simpl; unfold cores, active; simpl; split; auto.
  unfold proj_core in H2.
  if_tac in H2; try solve[congruence].
  if_tac in H2; try solve[congruence].
  unfold proj_core in H2.
  if_tac in H2; try solve[congruence].
  if_tac in H2; try solve[congruence].
  subst.
  solve[inv H2; auto].

  intros until m2'; intros H1 H2 H3.
  unfold active, cores in *.
  split; auto.
  unfold proj_core; auto.
  if_tac; auto.
  if_tac; auto.
  subst.
  unfold proj_core in H1.
  if_tac in H1; try congruence.
  inv H1.
  generalize (CSEM_FUN _ _ _ _ _ _ _ H2 H3).
  inversion 1; subst; auto.
  unfold proj_core in H1.
  if_tac in H1; try congruence.
  solve[if_tac in H1; try congruence].
  solve[elimtype False; auto].

  intros until m'; intros H1 H2.
  exists c'.
  unfold cores, active in H2.
  unfold proj_core in H1.
  if_tac in H1; try congruence.
  solve[if_tac in H1; try congruence].

  intros until m'; intros H1 H2 H3; intros j0; intros q r H4.
  unfold cores, active in *.
  unfold proj_core.
  if_tac; auto.
  if_tac; auto.
  subst.
  solve[elimtype False; omega].

  intros until n; intros H1 H2 H3 j0 q H4.
  unfold active, cores in *.
  unfold proj_core.
  if_tac; auto.
  solve[elimtype False; auto].

  intros until retv; intros H1 H2.
  exists c'.
  unfold cores, active in H1, H2.
  unfold proj_core in H1.
  if_tac in H1; try congruence.
  if_tac in H1; try congruence.
  inv H1.
  solve[split; auto].

  intros s s' retv H1 j q H2.
  unfold proj_core; auto.
  unfold active in H2.
  if_tac; auto.
  if_tac; auto.
  solve[elimtype False; auto].

  intros until args; intros H1.
  exists O; exists s.
  unfold active, cores, proj_core.
  solve[if_tac; try congruence; auto].
Qed.

Lemma null_owned_conserving: forall F V C D Z
       (csem: EffectfulSemantics (Genv.t F V) C D) (csig: ef_ext_spec mem Z),
  owned_conserving _ (const csem) (null_extension csem csig).
Proof.
  intros.
  unfold owned_conserving.
  intros.
  simpl in *.
  unfold proj_core in H.
  if_tac in H; try solve[congruence].
  if_tac in H; try solve[congruence].
  inv H.
  unfold const in H0.
  auto.
Qed.

Section NullExtensionCompilable.
 Variables 
  (fS vS fT vT cS cT dS dT Z: Type) 
  (csig: ef_ext_spec mem Z)
  (init_world: Z)
  (entry_points: list (val*val*signature))
  (csemS: EffectfulSemantics (Genv.t fS vS) cS dS)
  (csemT: EffectfulSemantics (Genv.t fT vT) cT dT).

 Variables (geS: Genv.t fS vS) (geT: Genv.t fT vT).

 Definition E_S: @Extension.Sig mem Z unit Z (Genv.t fS vS) dS cS csemS csig 
   _ _ (const cS) (const csemS) csig :=
  null_extension csemS csig.
 Definition E_T: @Extension.Sig mem Z unit Z (Genv.t fT vT) dT cT csemT csig 
   _ _ (const cT) (const csemT) csig :=
  null_extension csemT csig.

 Import Forward_simulation_inj_exposed.
 Import ExtensionCompilability2.

 Variable core_data: Type.
 Variable match_state: core_data -> reserve -> meminj -> cS -> mem -> cT -> mem -> Prop. 
 Variable core_ord: core_data -> core_data -> Prop.
 Variable core_simulation: Forward_simulation_inject dS dT csemS csemT 
   geS geT entry_points core_data match_state core_ord.
 Variable core_simulationsRG: forall i:nat, 
   RelyGuaranteeSimulation.Sig csemS csemT geS match_state.
 Variable threads_max: nat.
 Variable threads_max_nonzero: (O < threads_max)%nat. (*Required by defn. of core_ords*)

 Variable match_state_runnable: 
  forall cd r j s1 m1 s2 m2,
  match_state cd r j s1 m1 s2 m2 -> 
  rg_forward_simulations.runnable csemS s1=rg_forward_simulations.runnable csemT s2.

 Variable prog_compile_safe: 
   forall v1 vals1 c1 m1 r,
   make_initial_core csemS geS v1 vals1 = Some c1 -> 
   compile_safe.compile_safe csemS geS init_world r c1 m1.

 Lemma null_extension_compilable: 
   corestep_fun csemS -> corestep_fun csemT -> genvs_domain_eq geS geT -> 
   CompilableExtension.Sig csemS csemT geS geT entry_points.
 Proof.
 (*SOLVED BY econstructor; eauto.  WE'LL USE THE PROVIDED LEMMAS INSTEAD.*)
 intros H1 H2 H3.
 set (R := fun (_:reserve) (_:meminj) (_:cS) (_:mem) (_:cT) (_:mem) => True).
 destruct (@ExtensionCompilability
   _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
   csemS csemT csemS csemT csig csig 
   geS geT geS geT E_S E_T entry_points core_data match_state core_ord threads_max threads_max R)
  as [LEM].
 admit. (*will go away*)
 apply LEM; auto.
 solve[intros ? i; unfold const; apply genvs_domain_eq_refl; auto].
 solve[intros ? i; unfold const; apply genvs_domain_eq_refl; auto].
 unfold E_S, const.
 solve[apply (null_core_compatible geS csig H1)].
 unfold E_T, const.
 solve[apply (null_core_compatible geT csig H2)].
 solve[apply null_owned_conserving].
 solve[apply null_owned_conserving].
 
 constructor.
 assert (Extension.proj_core E_T (Extension.active E_T s') O s' = Some c').
  destruct (null_core_compatible geT csig H2).
  exploit (corestep_pres _ s c m c' s' m' m' H); eauto.
  intros [Heq0 [Heq ?]].
  simpl in Heq,Heq0|-*; rewrite Heq0 in *; rewrite <-Heq; auto.
  unfold proj_core in Heq.
  if_tac in Heq; try solve[congruence].
  solve[if_tac in Heq; try solve[congruence]].
 unfold const; simpl.
 simpl in H, H5; unfold proj_core in H, H5.
 assert (s = c).
  if_tac in H; try solve[congruence].
  if_tac in H; try solve[congruence].
 subst s.
 assert (s' = c').
  if_tac in H5; try solve[congruence].
  if_tac in H5; try solve[congruence].
 subst s'.
 solve[auto].

 assert (Extension.proj_core E_T (Extension.active E_T s') O s' = Some c').
  destruct (null_core_compatible geT csig H2).
  exploit (corestep_pres _ s c m c' s' m' m' H); eauto.
  intros [Heq0 [Heq ?]].
  simpl in Heq,Heq0|-*; rewrite Heq0 in *; rewrite <-Heq; auto.
  unfold proj_core in Heq.
  if_tac in Heq; try solve[congruence].
  solve[if_tac in Heq; try solve[congruence]].
 unfold const; simpl.
 simpl in H, H5; unfold proj_core in H, H5.
 assert (s = c).
  if_tac in H; try solve[congruence].
  if_tac in H; try solve[congruence].
 subst s.
 assert (s' = c').
  if_tac in H5; try solve[congruence].
  if_tac in H5; try solve[congruence].
 subst s'.
 solve[auto].

 constructor; try solve[intros; unfold R; auto]. 

 intros until j; intros H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15.
 inversion H4; subst.
 inversion H5; subst.
 apply corestep_not_at_external in H15.
 unfold const in H8; simpl in H8.
 unfold proj_core in H0.
 if_tac in H0; try congruence.
 solve[if_tac in H0; try congruence].

 intros until j; intros.
 unfold Extension.proj_core in *.
 simpl in *.
 unfold proj_core in *.
 if_tac in H0; try congruence.
 if_tac in H0; try congruence.
 inv H0.
 inv H4.
 destruct core_simulation.
 eapply core_at_external0 in H6; eauto.

 intros.
 solve[eapply mem_lemmas.forall_inject_valid; eauto].
 
 intros; destruct core_simulation; auto.
 destruct (core_initial0 v1 v2 sig H vals1 s1 m1 j vals2 r m2 H0 H4 H5 H6 H9 H10)
  as [cd [s2 [H11 H12]]]; auto.
 exists (fun _ _ => cd); exists s2; split; auto. 
 split; auto.

 intros i u c PROJ b ofs PRIV.
 unfold const in PRIV.
 elimtype False.
 simpl in PROJ.
 unfold proj_core in PROJ.
 if_tac in PROJ; try solve[congruence].
 if_tac in PROJ; try solve[congruence].
 subst.
 inv PROJ.
 solve[eapply (effects_initial _ b _ geS v1 vals1 c); eauto].

 split.
 unfold owned_disjoint.
 intros i j0 i' j' c d NEQ; simpl; intros PROJ1 PROJ2 b PRIV CONTRA.
 unfold proj_core in *.
 if_tac in PROJ1; try solve[congruence]. 
 if_tac in PROJ1; try solve[congruence]. 
 inv PROJ1.
 solve[if_tac in PROJ2; try solve[congruence]]. 

 split.
 intros i j0 c PROJ b ofs PRIV.
 unfold const in PRIV.
 elimtype False.
 simpl in PROJ.
 unfold proj_core in PROJ.
 if_tac in PROJ; try solve[congruence].
 inv PROJ.
 if_tac in H15; try solve[congruence].
 inv H15.
 solve[eapply (effects_initial _ b _ geT v2 vals2 c); eauto].

 split.
 unfold owned_disjoint.
 intros i j0 i' j' c d NEQ; simpl; intros PROJ1 PROJ2 b PRIV CONTRA.
 unfold proj_core in *.
 if_tac in PROJ1; try solve[congruence]. 
 if_tac in PROJ1; try solve[congruence]. 
 inv PROJ1.
 solve[if_tac in PROJ2; try solve[congruence]]. 
 
 split; auto.
 split; auto.

 split.
 exploit effects_valid0; eauto.
 solve[intros [? ?]; auto].
 split.
 exploit effects_valid0; eauto.
 solve[intros [? ?]; auto].
 split.
 solve[exploit match_memwd0; eauto].
 split.
 solve[exploit match_memwd0; eauto].
 split.
 intros b ofs ? ? EF.
 elimtype False.
 solve[eapply effects_initial in H0; eauto].
 split.
 intros b ofs ? ? EF.
 elimtype False.
 solve[eapply effects_initial in H11; eauto].
 split.
 intros b ofs ofs2 delta ? ?.
 solve[eapply allocs_only_shrink0; eauto].
 split.
 solve[unfold R; auto].
 split; auto.
 split.
 
 intros u c1 ACT.
 split.
 intros b ofs ? ? EF.
 elimtype False.
 unfold const in EF; simpl in EF.
 simpl in ACT.
 unfold proj_core in ACT.
 if_tac in ACT; try solve[congruence].
 if_tac in ACT; try solve[congruence].
 inversion ACT.
 subst c1.
 solve[eapply effects_initial in H0; eauto].
 split.
 exists init_world.
 simpl in ACT.
 unfold proj_core in ACT.
 if_tac in ACT; try solve[congruence].
 if_tac in ACT; try solve[congruence].
 inversion ACT.
 subst c1.
 solve[eapply prog_compile_safe; eauto]. (*potentially need to know something about v1, vals1 here*)
 exists s2.
 split; auto.

 simpl in ACT|-*.
 unfold proj_core in ACT|-*.
 if_tac in ACT; try congruence.
 if_tac in ACT; try congruence.
 solve[auto].

 split.
 intros b ofs ? ? EF.
 elimtype False.
 solve[eapply effects_initial in H11; eauto].

 simpl in ACT.
 unfold proj_core in ACT.
 if_tac in ACT; try solve[congruence].
 if_tac in ACT; try solve[congruence].
 inversion ACT.
 solve[subst c1; auto].

 intros i u c1 H9'' H9'; exists s2; split; auto.
 simpl in H9'; unfold proj_core in H9'|-*; if_tac in H9'; try congruence.
 simpl; unfold proj_core; rewrite H13; if_tac; auto.
 solve[elimtype False; auto].
 simpl in H9'; unfold proj_core in H9'.
 if_tac in H9'; try congruence.
 exists cd, r, j, m1, m2.
 split.
 intros b ofs ? ? EF.
 elimtype False.
 eapply effects_initial 
   with (k := ModifyEffect) (b0 := b) (ofs0 := ofs) in H0; eauto.
 simpl in H9'; unfold proj_core in H9'.
 if_tac in H9'; try congruence.
 if_tac in H9'; try congruence.
 subst.
 simpl in H9''.
 unfold active in H9''.
 solve[auto].
 split.
 exists init_world.
 simpl in H9'.
 unfold proj_core in H9'.
 if_tac in H9'; try congruence.
 if_tac in H9'; try congruence.
 inv H9'.
 solve[eapply prog_compile_safe; eauto].
 split; auto.
 intros b ofs ? ? EF.
 elimtype False.
 solve[eapply effects_initial 
   with (k := ModifyEffect) (b0 := b) (ofs0 := ofs) in H11; eauto].

 unfold const.
 simpl in H9'; unfold  proj_core in H9'.
 if_tac in H9'; try congruence.
 solve[if_tac in H9'; try congruence].

 intros until v1; intros ty MATCH12 HALT HASTY.
 unfold CompilabilityInvariant.match_states, const in MATCH12.
 destruct MATCH12 as [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [MATCH12 ?]]]]]]]]]]]]]]]].
 specialize (MATCH12 O c1).
 spec MATCH12; auto.
 destruct MATCH12 as [GR [? [c2' [PROJ [GR' MATCH12]]]]].
 simpl in PROJ; unfold proj_core in PROJ; inv PROJ.
 destruct core_simulation.
 solve[eapply core_halted0 in HALT; eauto].

 intros; destruct core_simulation.
 apply corestep_not_halted in H6.
 simpl in H0; unfold proj_core, active in H0.
 if_tac in H0; try congruence.
 if_tac in H0; try congruence.
 inv H0.
 solve[simpl in H5; unfold const in H5; rewrite H5 in H6; congruence].
 Qed.

End NullExtensionCompilable.
