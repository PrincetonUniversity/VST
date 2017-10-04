Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.forward_simulations.
Require Import sepcomp.step_lemmas.
Require Import sepcomp.extspec.
Require Import sepcomp.linking.
Require Import sepcomp.linking_simulations.
Require Import sepcomp.Coqlib2.
Require Import sepcomp.wf_lemmas.

Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Events.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.

Set Implicit Arguments.

(* use this "remember" tactic instead of the standard library one *)
Tactic Notation "remember" constr(a) "as" ident(x) :=
   let x := fresh x in
  let H := fresh "Heq" x in
  (set (x:=a) in *; assert (H: x=a) by reflexivity; clearbody x).

Lemma runnable_false (G C M (*D*): Type) (csem: CoreSemantics G C M (*D*)):
 forall c, runnable csem c=false ->
 (exists rv, halted csem c = Some rv) \/
 (exists ef, exists sig, exists args,
   at_external csem c = Some (ef, sig, args)).
Proof.
intros c; unfold runnable.
destruct (at_external csem c).
destruct p as [[ef sig] vals].
intros; right; do 2 eexists; eauto.
destruct (halted csem c).
intros; left; eexists; eauto.
congruence.
Qed.
(*
Lemma genvs_domain_eq_refl: forall F V (ge: Genv.t F V), genvs_domain_eq ge ge.
Proof. solve[intros F V ge; unfold genvs_domain_eq; split; intro b; split; auto]. Qed.
*)
Section CoreCompatibleLemmas. Variables
 (Z: Type) (** external states *)
 (Zint: Type) (** portion of Z implemented by extension *)
 (Zext: Type) (** portion of Z external to extension *)
 (G: Type) (** global environments of extended semantics *)
 (xT: Type) (** corestates of extended semantics *)
 (esem: CoopCoreSem G xT) (** extended semantics *)
 (esig: ef_ext_spec mem Zext) (** extension signature *)
 (gT: Type) (** global environments of core semantics *)
 (cT: Type) (** corestates of core semantics *)
 (csem: CoopCoreSem gT cT)
 (csig: ef_ext_spec mem Z). (** client signature *)

Variables (ge: G) (ge_core: gT).
Variable E: Extension.Sig Z Zint Zext esem gT cT csem.

Variable Hcore_compatible: core_compatible ge ge_core E.

Import Extension.

Lemma zint_invar_over_corestepN:
  forall n s m s' m',
  corestepN csem ge_core n (proj_core E s) m (proj_core E s') m' ->
  corestepN esem ge n s m s' m' ->
  proj_zint E s=proj_zint E s'.
Proof.
intros.
revert s m H H0.
induction n.
simpl.
intros.
inv H0.
solve[auto].
intros s2 m2.
simpl.
intros [x [m0 [H1 H2]]].
intros [x' [m0' [H1' H2']]].
assert (proj_core E x' = x).
 inv Hcore_compatible.
 eapply corestep_pres in H1; eauto.
 solve[destruct H1; auto].
assert (m0 = m0').
 rewrite <-H in H1.
 inv Hcore_compatible.
 eapply corestep_pres with (m'' := m0') in H1; eauto.
 solve[destruct H1; auto].
subst m0.
eapply zint_invar_over_corestep in H1'.
rewrite H1'.
eapply IHn; eauto.
solve[rewrite H; auto].
rewrite H; eauto.
Qed.

Lemma corestepN_pres: forall n s m c' s' m' m'',
   corestepN csem ge_core n (proj_core E s) m c' m' ->
   corestepN esem ge n s m s' m'' ->
   proj_core E s' = c' /\ m'=m''.
Proof.
intros.
revert s m H H0.
induction n.
simpl.
intros.
inv H0.
solve[split; inv H; auto].
intros s m.
simpl.
intros [c2 [m2 [STEP STEPN]]].
intros [st2 [m2' [CSTEP CSTEPN]]].
assert (proj_core E st2 = c2 /\ m2' = m2).
 inv Hcore_compatible.
 eapply corestep_pres with (m'' := m2') in STEP.
 destruct STEP. subst m2'.
 rewrite H.
 solve[split; auto].
 solve[auto].
eapply IHn; eauto.
solve[destruct H; subst c2; subst m2'; auto].
Qed.

Lemma corestep_step:
  forall s m c' m',
  let c := proj_core E s in
  corestep csem ge_core c m c' m' ->
  exists s',
    corestep esem ge s m s' m' /\
    proj_core E s' = c'.
Proof.
intros until m'; intros H0 H1.
inv Hcore_compatible.
generalize H1 as H1'; intro.
eapply corestep_prog in H1; eauto.
Qed.

Lemma corestep_stepN:
  forall n s m c' m',
  let c := proj_core E s in
  corestepN csem ge_core n c m c' m' ->
  exists s',
    corestepN esem ge n s m s' m' /\
    proj_core E s' = c'.
Proof.
inv Hcore_compatible.
generalize corestep_step; intro H1.
intros n.
induction n; auto.
intros until m'.
intros H0 H2.
inv H2.
simpl.
exists s.
split; auto.
intros.
simpl in H.
destruct H as [c2 [m2 [H5 H6]]].
eapply H1 in H5; eauto.
destruct H5 as [s2 [H5 H7]].
destruct (IHn s2 m2 c' m') as [s' [H10 H11]]; auto.
rewrite H7.
auto.
exists s'.
split; auto.
simpl.
exists s2; exists m2; split; eauto.
Qed.

Lemma corestep_step_star:
  forall s m c' m',
  let c := proj_core E s in
  corestep_star csem ge_core c m c' m' ->
  exists s',
    corestep_star esem ge s m s' m' /\
    proj_core E s' = c'.
Proof.
intros until m'; intros H0 H1.
destruct H1 as [n H1].
eapply corestep_stepN in H1; eauto.
destruct H1 as [s' [H1 H2]].
exists s'.
split; auto.
solve[exists n; eauto].
Qed.

Lemma corestep_step_plus:
  forall s m c' m',
  let c := proj_core E s in
  corestep_plus csem ge_core c m c' m' ->
  exists s',
    corestep_plus esem ge s m s' m' /\
    proj_core E s' = c'.
Proof.
intros until m'; intros H0 H1.
destruct H1 as [n H1].
eapply corestep_stepN in H1; eauto.
destruct H1 as [s' [H1 H2]].
exists s'.
split; auto.
solve[exists n; eauto].
Qed.

End CoreCompatibleLemmas.

Module ExtendedSimulations. Section ExtendedSimulations.
 Variables
  (F_S V_S F_T V_T: Type) (** source and target extension global environments *)
  (xS xT: Type) (** corestates of source and target extended semantics *)
  (fS fT vS vT: Type) (** global environments of core semantics *)
  (cS cT: Type) (** corestates of source and target core semantics *)
  (Z: Type) (** external states *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type) (** portion of Z external to extension *)
  (esemS: CoopCoreSem (Genv.t F_S V_S) xS) (** extended source semantics *)
  (esemT: CoopCoreSem (Genv.t F_T V_T) xT) (** extended target semantics *)
  (csemS: CoopCoreSem (Genv.t fS vS) cS)
  (csemT: CoopCoreSem (Genv.t fT vT) cT)
  (csig: ef_ext_spec mem Z) (** client signature *)
  (esig: ef_ext_spec mem Zext). (** extension signature *)

 Variables
  (ge_S: Genv.t F_S V_S) (ge_T: Genv.t F_T V_T)
  (ge_coreS: Genv.t fS vS)
  (ge_coreT: Genv.t fT vT).

 Variable (E_S: @Extension.Sig mem Z Zint Zext (Genv.t F_S V_S)
                               xS esemS _ cS csemS).
 Variable (E_T: @Extension.Sig mem Z Zint Zext (Genv.t F_T V_T)
                               xT esemT _ cT csemT).
 Variable entry_points: list (val*val*signature).

 Notation PROJ_CORE := (Extension.proj_core).
 Infix "\o" := (Extension.zmult) (at level 66, left associativity).
 Notation zint_invar_after_external := (Extension.zint_invar_after_external).

 Variable core_data: Type.
 Variable match_state: core_data -> meminj -> cS -> mem -> cT -> mem -> Prop.
 Variable core_ord: core_data -> core_data -> Prop.
 Implicit Arguments match_state [].
 Implicit Arguments core_ord [].

 Import Forward_simulation_inj_exposed.

 Variable genvs_dom_eq_ST: genvs_domain_eq ge_S ge_T.

 Variable core_simulation:
   Forward_simulation_inject csemS csemT ge_coreS ge_coreT
   entry_points core_data match_state core_ord.

 Definition match_states (cd: core_data) (j: meminj) (s1: xS) m1 (s2: xT) m2 :=
   match_state cd j (PROJ_CORE E_S s1) m1 (PROJ_CORE E_T s2) m2 /\
   Extension.proj_zint E_S s1 = Extension.proj_zint E_T s2.

 Inductive internal_compilability_invariant: Type :=
   InternalCompilabilityInvariant: forall

  (match_state_runnable: forall cd j c1 m1 c2 m2,
    match_state cd j c1 m1 c2 m2 -> runnable csemS c1=runnable csemT c2)

  (match_state_inj: forall cd j c1 m1 c2 m2,
    match_state cd j c1 m1 c2 m2 -> Mem.inject j m1 m2)

  (match_state_preserves_globals: forall cd j c1 m1 c2 m2,
    match_state cd j c1 m1 c2 m2 ->
    Events.meminj_preserves_globals ge_coreS j)

 (extension_diagram: forall s1 m1 s1' m1' s2 m2 ef sig args1 args2 cd j,
   let c1 := PROJ_CORE E_S s1 in
   let c2 := PROJ_CORE E_T s2 in
   runnable csemS c1=false ->
   runnable csemT c2=false ->
   at_external csemS c1 = Some (ef, sig, args1) ->
   at_external csemT c2 = Some (ef, sig, args2) ->
   match_states cd j s1 m1 s2 m2 ->
   Mem.inject j m1 m2 ->
   Events.meminj_preserves_globals ge_S j ->
   Forall2 (val_inject j) args1 args2 ->
   corestep esemS ge_S s1 m1 s1' m1' ->
   exists s2', exists m2', exists cd', exists j',
     inject_incr j j' /\
     Events.inject_separated j j' m1 m2 /\
     match_states cd' j' s1' m1' s2' m2' /\
     Mem.unchanged_on (Events.loc_unmapped j) m1 m1' /\
     Mem.unchanged_on (Events.loc_out_of_reach j m1) m2 m2' /\
     ((corestep_plus esemT ge_T s2 m2 s2' m2') \/
      corestep_star esemT ge_T s2 m2 s2' m2' /\ core_ord cd' cd))

 (at_external_match: forall s1 m1 s2 m2 ef sig args1 args2 cd j,
   let c1 := PROJ_CORE E_S s1 in
   let c2 := PROJ_CORE E_T s2 in
   runnable csemS c1=runnable csemT c2 ->
   at_external esemS s1 = Some (ef, sig, args1) ->
   at_external csemS c1 = Some (ef, sig, args1) ->
   match_state cd j c1 m1 c2 m2 ->
   Mem.inject j m1 m2 ->
   Events.meminj_preserves_globals ge_S j ->
   Forall2 (val_inject j) args1 args2 ->
   at_external csemT c2 = Some (ef, sig, args2) ->
   at_external esemT s2 = Some (ef, sig, args2))

  (initial_diagram: forall v1 vals1 s1 m1 v2 vals2 m2 j sig,
    In (v1, v2, sig) entry_points ->
    initial_core esemS ge_S v1 vals1 = Some s1 ->
    Mem.inject j m1 m2 ->
    Forall2 (val_inject j) vals1 vals2 ->
    exists cd, exists s2,
      initial_core esemT ge_T v2 vals2 = Some s2 /\
      match_states cd j s1 m1 s2 m2)

 (halted_diagram: forall cd j c1 m1 c2 m2 v1,
   match_states cd j c1 m1 c2 m2 ->
   halted esemS c1 = Some v1 ->
   exists v2, val_inject j v1 v2 /\
     halted esemT c2 = Some v2 /\
     Mem.inject j m1 m2),
  internal_compilability_invariant.

 Variables
  (esig_compilable: internal_compilability_invariant)
  (genvs_domain_eqS: genvs_domain_eq ge_S ge_coreS)
  (genvs_domain_eqT: genvs_domain_eq ge_T ge_coreT)
  (core_compatS: core_compatible ge_S ge_coreS E_S)
  (core_compatT: core_compatible ge_T ge_coreT E_T).

Program Definition extended_simulation:
  Forward_simulation_inject esemS esemT ge_S ge_T
           entry_points core_data match_states core_ord:=
  @Build_Forward_simulation_inject _ _ _ _ _ _
           esemS esemT ge_S ge_T entry_points
           core_data match_states core_ord
           _ _ _ _ _ _ _ _ _ .
Next Obligation.
destruct core_simulation; auto.
Qed.
Next Obligation.
destruct core_simulation; auto.
destruct H.
eapply match_validblocks0; eauto.
Qed.
Next Obligation.
destruct core_simulation.
unfold match_states in H.
destruct H as [H H0].
apply match_genv0 in H.
clear - genvs_domain_eqS H.
rewrite <-meminj_preserves_genv2blocks.
erewrite genvs_domain_eq_preserves; eauto.
rewrite meminj_preserves_genv2blocks.
auto.
Qed.
Next Obligation.
rename H0 into MATCH.
generalize MATCH as MATCH'; intro.
unfold match_states in MATCH.
rename H into STEP.
case_eq (runnable csemS (PROJ_CORE E_S st1)).

(*Case 1: runnable thread, appeal to core diagram for cores*)
intros RUN1.
assert (RUN2: runnable csemT (PROJ_CORE E_T st2)=true).
 inv esig_compilable.
 rewrite match_state_runnable
  with (cd := cd) (j := j) (m1 := m1) (c2 := PROJ_CORE E_T st2) (m2 := m2) in RUN1.
 auto.
 destruct MATCH as [MATCH XX].
 solve[auto].
assert (corestep csemS ge_coreS (PROJ_CORE E_S st1) m1 (PROJ_CORE E_S st1') m1').
 inv esig_compilable.
 inv core_compatS.
 specialize (runnable_corestep st1 m1 st1' m1' RUN1 STEP).
 solve[auto].

destruct core_simulation.
rename core_diagram0 into DIAG.
destruct MATCH as [MATCH XX].
specialize (DIAG (PROJ_CORE E_S st1) m1 (PROJ_CORE E_S st1') m1' H
                 cd (PROJ_CORE E_T st2) j m2 MATCH).
destruct DIAG as [c2' [m2' [cd' [j' [INJ_INCR [INJ_SEP [MATCH'' STEP2]]]]]]].
destruct STEP2 as [STEP2|STEP2].

(*corestep_plus case*)
destruct STEP2 as [n STEP2].
generalize (corestep_stepN _ _ core_compatT) as CSTEPN; intro.
specialize (CSTEPN (S n) st2).
specialize (CSTEPN m2 c2' m2').
simpl in CSTEPN.
spec CSTEPN.
simpl in STEP2.
destruct STEP2 as [c2'' [m2'' [STEP2 STEPN2]]].
exists c2'', m2''.
solve[split; auto].
destruct CSTEPN as [st2'' [[c2'' [m2'' [? ?]]] ?]].
exists st2'', m2', cd', j'.
split; auto.
split; auto.
split.
unfold match_states; auto.
rewrite H2.
split; auto.
symmetry.
eapply Extension.zint_invar_over_corestep in STEP; eauto.
rewrite <-STEP.
assert (Extension.proj_zint E_T st2'' =
        Extension.proj_zint E_T st2) as ->.
  simpl in STEP2.
  destruct STEP2 as [? [? [S1 S2]]].
  assert (PROJ_CORE E_T c2'' = x /\ m2'' = x0).
    inv core_compatT.
    eapply corestep_pres in S1; eauto.
    destruct S1. solve[split; auto].
  destruct H3.
  subst m2''; subst x.
  eapply zint_invar_over_corestepN in H1; eauto.
  rewrite <-H1.
  eapply Extension.zint_invar_over_corestep in H0; eauto.
  solve[subst c2'; auto].
solve[auto].
left.
exists n. simpl. exists c2'', m2''. split; auto.

(*corestep_star case*)
destruct STEP2 as [[n STEP2] CORE_ORD].
generalize (corestep_stepN _ _ core_compatT) as CSTEPN; intro.
specialize (CSTEPN n st2).
specialize (CSTEPN m2 c2' m2').
simpl in CSTEPN.
spec CSTEPN.
simpl in STEP2.
destruct n.
solve[simpl in STEP2|-*; auto].
simpl in STEP2.
destruct STEP2 as [c2'' [m2'' [STEP2 STEPN2]]].
exists c2'', m2''.
solve[split; auto].
destruct CSTEPN as [st2'' [STEP2N PROJ]].
exists st2'', m2', cd', j'.
split; auto.
split; auto.
split.
unfold match_states; auto.
rewrite PROJ.
split; auto.
symmetry.
eapply Extension.zint_invar_over_corestep in STEP; eauto.
rewrite <-STEP.
assert (Extension.proj_zint E_T st2'' =
        Extension.proj_zint E_T st2) as ->.
  eapply zint_invar_over_corestepN in STEP2N; eauto.
  rewrite PROJ.
  solve[auto].
solve[auto].
right.
split; auto.
exists n; auto.

(*runnable = false*)
intros RUN1.
generalize RUN1 as RUN1'; intro.
apply runnable_false in RUN1.
destruct RUN1 as [[rv1 HALT]|[ef [sig [args AT_EXT]]]].

(*active thread is safely halted*)
rename MATCH into MATCH12.
assert (halted esemS st1 = Some rv1).
 inv core_compatS.
 solve[rewrite halted_proj; auto].
apply corestep_not_halted in STEP.
rewrite STEP in H.
congruence.
rename MATCH into MATCH12.
destruct core_simulation.
clear
 core_after_external0
 core_halted0
 core_initial0
 core_diagram0.
generalize MATCH12 as MATCH12'; intro.
destruct MATCH12 as [MATCH12 XX].
specialize (@core_at_external0 _ _ _ _ _ _ _ _ _ MATCH12 AT_EXT).
(*spec core_at_external0.
solve[eapply at_extern_valid; eauto].*)
destruct core_at_external0
 as [INJ [GLOB [val2 [INJ1 ATEXT]]]].
assert (RUN2': runnable csemT (PROJ_CORE E_T st2) = false).
 unfold runnable.
 solve[rewrite ATEXT; auto].
inv esig_compilable.
clear
 match_state_runnable
 match_state_inj
 halted_diagram.
rewrite <-meminj_preserves_genv2blocks in GLOB.
eapply genvs_domain_eq_preserves in genvs_domain_eqS.
rewrite <-genvs_domain_eqS in GLOB.
rewrite meminj_preserves_genv2blocks in GLOB.
specialize (extension_diagram
 _ _ _ _ _ _ _ _ _ _ _ _
 RUN1' RUN2'
 AT_EXT ATEXT
 MATCH12'
 INJ GLOB INJ1
 STEP).
destruct extension_diagram
 as [s2' [m2' [cd' [j' [? [? [? [? [? ?]]]]]]]]].
exists s2', m2', cd', j'.
solve[split; auto].
Qed.
Next Obligation.
inv esig_compilable.
eapply initial_diagram; eauto.
Qed.
Next Obligation.
inv esig_compilable.
eapply halted_diagram; eauto.
Qed.
Next Obligation.
destruct core_simulation.
clear
 core_after_external0
 core_halted0
 core_initial0
 core_diagram0.
inv esig_compilable.
generalize H0 as H0'; intro.
inv core_compatS.
apply at_external_proj in H0.
generalize H as H'; intro.
destruct H as [H XX].
specialize (core_at_external0
 _ _ _ _ _ _ _ _ _
 H H0).
destruct core_at_external0 as [? [? [vals2 [? ?]]]].
rewrite <-meminj_preserves_genv2blocks in H2.
eapply genvs_domain_eq_preserves in genvs_domain_eqS.
rewrite <-genvs_domain_eqS in H2.
rewrite meminj_preserves_genv2blocks in H2.
split; auto.
split; auto.
exists vals2.
split; auto.
solve[exploit at_external_match; eauto].
Qed.
Next Obligation.
destruct core_simulation.
clear
 core_halted0
 core_initial0
 core_diagram0.
inv esig_compilable.
generalize H1 as H1'; intro.
assert (H2': exists vals2, at_external esemT st2 = Some (e, ef_sig, vals2)).
 inv core_compatS.
 apply at_external_proj in H1.
 destruct H0.
 specialize (core_at_external0 _ _ _ _ _ _ _ _ _ H0 H1).
 destruct core_at_external0 as [? [? [vals2 [? ?]]]].
 exists vals2.
 solve[eapply at_external_match; eauto].
inv core_compatS.
apply at_external_proj in H1.
assert (H3': meminj_preserves_globals ge_coreS j).
 rewrite <-meminj_preserves_genv2blocks in H2.
 eapply genvs_domain_eq_preserves in genvs_domain_eqS.
 rewrite genvs_domain_eqS in H2.
 rewrite meminj_preserves_genv2blocks in H2.
 solve[auto].
destruct H0 as [H0 XX].
specialize (core_after_external0
 _ _ _ _ _ _ _ _ _ _ _ _ _ _
 H H0 H1 H3' H3 H4 H5 H6 H7 H8 H9 H10).
destruct H2' as [vals2 H2'].
destruct core_after_external0
 as [cd' [c1' [c2' [AFTER1 [AFTER2 MATCH]]]]].
apply after_ext_prog in AFTER1.
inv core_compatT.
apply after_ext_prog0 in AFTER2.
exists cd'.
destruct AFTER1 as [s1' [? ?]].
destruct AFTER2 as [s2' [? ?]].
exists s1', s2'; split; auto.
split; auto.
unfold match_states.
rewrite H12, H14.
split; auto.
symmetry.
eapply Extension.zint_invar_after_external in H11; eauto.
rewrite <-H11.
eapply Extension.zint_invar_after_external in H13; eauto.
rewrite <-H13.
auto.
Qed.

End ExtendedSimulations. End ExtendedSimulations.

Module ExtensionCompilability. Section ExtensionCompilability.
 Variables
  (F_S V_S F_T V_T: Type) (** source and target extension global environments *)
  (xS xT: Type) (** corestates of source and target extended semantics *)
  (fS fT vS vT: Type) (** global environments of core semantics *)
  (cS cT: Type) (** corestates of source and target core semantics *)
  (Z: Type) (** external states *)
  (Zint: Type) (** portion of Z implemented by extension *)
  (Zext: Type) (** portion of Z external to extension *)
  (esemS: CoopCoreSem (Genv.t F_S V_S) xS) (** extended source semantics *)
  (esemT: CoopCoreSem (Genv.t F_T V_T) xT) (** extended target semantics *)
  (csemS: CoopCoreSem (Genv.t fS vS) cS) (** a set of core semantics *)
  (csemT: CoopCoreSem (Genv.t fT vT) cT) (** a set of core semantics *)
  (csig: ef_ext_spec mem Z) (** client signature *)
  (esig: ef_ext_spec mem Zext). (** extension signature *)

 Variables
  (ge_S: Genv.t F_S V_S) (ge_T: Genv.t F_T V_T)
  (ge_coreS: Genv.t fS vS) (ge_coreT: Genv.t fT vT).

 Variable (E_S: @Extension.Sig mem Z Zint Zext (Genv.t F_S V_S) xS esemS _ cS csemS).
 Variable (E_T: @Extension.Sig mem Z Zint Zext (Genv.t F_T V_T) xT esemT _ cT csemT).

 Variable entry_points: list (val*val*signature).
 Variable core_data: Type.
 Variable match_state: core_data -> meminj -> cS -> mem -> cT -> mem -> Prop.
 Implicit Arguments match_state [].
 Variable core_ord: core_data -> core_data -> Prop.

 Import Extension.

 Definition match_states (cd: core_data) (j: meminj) (s1: xS) m1 (s2: xT) m2 :=
   match_state cd j (proj_core E_S s1) m1 (proj_core E_T s2) m2.

 Import Forward_simulation_inj_exposed.

 Lemma ExtensionCompilability:
   EXTENSION_COMPILABILITY.Sig
     esemS esemT csemS csemT ge_S ge_T ge_coreS ge_coreT E_S E_T
     entry_points match_state core_ord.
 Proof.
 eapply @EXTENSION_COMPILABILITY.Make.
 intros core_simulations H8 H9 H10 H11 H12 H13.
 eapply CompilableExtension.Make.
 eapply ExtendedSimulations.extended_simulation; eauto.
 solve[inv H13; constructor; auto].
Qed.

End ExtensionCompilability. End ExtensionCompilability.
