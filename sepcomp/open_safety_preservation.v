(*CompCert imports*)
Require Import compcert.common.Events.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.Values.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.

Require Import msl.Axioms.
Require Import sepcomp.extspec.
Require Import sepcomp.mem_lemmas. (*needed for definition of mem_forward etc*)
Require Import sepcomp.step_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.effect_semantics.
Require Import sepcomp.effect_simulations.
Require Import sepcomp.StructuredInjections.

Import SM_simulation.

(** * Safety and semantics preservation *)

Section safety_preservation_lemmas.
Context  {F V TF TV C D Z : Type}
         {source : @EffectSem (Genv.t F V) C}
         {target : @EffectSem (Genv.t TF TV) D}
         {geS : Genv.t F V}
         {geT : Genv.t TF TV}
         {entry_points : list (val*val*signature)}

  (sim : SM_simulation_inject source target geS geT entry_points)
  (z : Z)
  (c : C)
  (d : D)
  (m : mem)
  (tm: mem)

  (spec : ext_spec Z)
  (spec_closed : injection_closed spec)

  (SRC_DET : corestep_fun source)

  (TGT_DET : corestep_fun target)
  
  (source_safe : forall n, safeN source spec geS n z c m)
.

Notation data := (sim.(SM_simulation.core_data _ _ _ _ _)).
Notation ord  := (sim.(SM_simulation.core_ord _ _ _ _ _)).
Notation match_state := (sim.(SM_simulation.match_state _ _ _ _ _)).

Definition my_P := fun (x: data) => 
  forall (j : SM_Injection) (z : Z) (c : C) (d : D) (m tm : mem),
  (forall n : nat, safeN source spec geS n z c m) ->
  match_state x j c m d tm ->
  (exists ef sig vals, at_external source c = Some (ef, sig, vals))
   \/ ((exists rv, halted source c = Some rv) \/
       (exists cd' j' c' m',
         corestep_plus source geS c m c' m'
         /\ ((exists d' tm', corestep_plus target geT d tm d' tm'
              /\ match_state cd' j' c' m' d' tm')
         \/ (exists rv, halted source c' = Some rv 
              /\ match_state cd' j' c' m' d tm)
         \/ (exists ef sig vals, 
               at_external source c' = Some (ef, sig, vals)
              /\ match_state cd' j' c' m' d tm)))).

Lemma corestep_ord:
  forall cd j,
  match_state cd j c m d tm -> 
  (exists ef sig vals, at_external source c = Some (ef, sig, vals))
   \/ (exists rv, halted source c = Some rv) 
   \/ (exists cd' j' c' m',
         corestep_plus source geS c m c' m'
         /\ ((exists d' tm', corestep_plus target geT d tm d' tm'
                          /\ match_state cd' j' c' m' d' tm')
          \/ (exists rv, halted source c' = Some rv 
                          /\ match_state cd' j' c' m' d tm)
          \/ (exists ef sig vals, 
                at_external source c' = Some (ef, sig, vals)
                          /\ match_state cd' j' c' m' d tm))).
Proof.
assert (my_well_founded_induction
     : (forall x, (forall y, ord y x -> my_P y) -> my_P x) ->
       forall a, my_P a).
  solve[apply well_founded_induction; destruct sim; auto].
unfold my_P in my_well_founded_induction.
destruct sim; simpl in *.
intros cd j H; simpl.
clear match_validblocks0 core_halted0 
  core_initial0 core_at_external0 eff_after_external0.
revert j z c d m tm source_safe H.
apply my_well_founded_induction; auto.
intros.
case_eq (at_external source c).
{ intros [[ef sig] args] AT_EXT.
  left; exists ef, sig, args; auto. }
intros AT_EXT.
case_eq (halted source c).
intros.
solve[right; left; exists v; auto].
intros HALTED_NONE.
generalize H0 as SAFE; intro.
specialize (H0 (S O)); simpl in H0.
rewrite HALTED_NONE in H0.
case_eq (at_external source c).
intros [[ef sig] args] AT_EXT'.
rewrite AT_EXT' in AT_EXT; congruence.
intros AT_EXT'; rewrite AT_EXT' in H0.
destruct H0 as [c2 [m2 [STEP _]]].
generalize STEP as STEP'; intro.
eapply core_diagram0 in STEP; eauto.
clear AT_EXT.
destruct STEP as [d2 [tm2 [cd2 [j2 [? [? [? [? [? [? H2]]]]]]]]]].
destruct H2.
right; right.
exists cd2, j2, c2, m2.
split; auto.
solve[exists O; simpl; exists c2, m2; split; auto].
solve[left; exists d2, tm2; split; auto].
destruct H2 as [H2 ORD].
specialize (H _ ORD j2 z c2 d2 m2 tm2).
assert (SAFE': forall n, safeN source spec geS n z c2 m2).
  solve[intros n; eapply safe_corestep_forward; eauto].
specialize (H SAFE' H5).
destruct H2 as [n H2].
destruct n. inv H2.
destruct H.
destruct H as [ef [sig [args AT_EXT]]].
right; right.
exists cd2, j2, c2, m2.
split; auto.
solve[exists O; simpl; exists c2, m2; split; auto].
solve[right; right; exists ef, sig, args; auto].
destruct H.
destruct H as [rv HALTED].
right; right.
exists cd2, j2, c2, m2.
split; auto.
solve[exists O; simpl; exists c2, m2; split; auto].
solve[right; left; exists rv; split; auto].
destruct H as [cd' [j' [c' [m' [STEPN H]]]]].
destruct H as [H|[H|H]].
destruct H as [d' [tm' [TSTEP' MATCH']]].
right; right.
exists cd', j', c', m'.
split; auto. 
destruct STEPN as [n STEPN].
exists (S n).
simpl.
exists c2, m2.
split; auto.
solve[left; exists d', tm'; split; auto].
destruct H as [rv [HALT MATCH']].
right; right.
exists cd', j', c', m'.
split; auto. 
destruct STEPN as [n STEPN].
exists (S n).
simpl.
exists c2, m2.
split; auto.
solve[right; left; exists rv; split; auto].
destruct H as [ef [sig [args AT_EXT]]].
right; right.
exists cd', j', c', m'.
split; auto. 
destruct STEPN as [n STEPN].
exists (S n).
simpl.
exists c2, m2.
split; auto.
solve[right; right; exists ef, sig, args; auto].
right; right.
exists cd2, j2, c2, m2.
split; auto. 
solve[exists O; simpl; exists c2, m2; split; auto].
left. 
exists d2, tm2.
split; auto.
exists n; auto.
Qed.

Notation EXIT z rv m := (ext_spec_exit spec (Some rv) z m).
Notation P ef x tys vals z m  := (ext_spec_pre spec ef x tys vals z m).

Definition halt_match z c m d tm := 
  exists rv trv, 
    halted source c = Some rv 
    /\ halted target d = Some trv
    /\ EXIT z rv m 
    /\ EXIT z trv tm.

Definition at_external_match z c m d tm :=
  exists ef sig x tys vals tvals,
    at_external source c = Some (ef, sig, vals) 
    /\ at_external target d = Some (ef, sig, tvals)
    /\ P ef x tys vals z m
    /\ P ef x tys tvals z tm.

Lemma corestep_ord':
  forall cd j,
  match_state cd j c m d tm -> 
  at_external_match z c m d tm
  \/ halt_match z c m d tm 
  \/ (exists cd' j' c' m', 
         corestep_plus source geS c m c' m' /\ 
               ((match_state cd' j' c' m' d tm /\ at_external_match z c' m' d tm)
            \/ ((match_state cd' j' c' m' d tm /\ halt_match z c' m' d tm)
            \/ (exists d' tm', 
                  corestep_plus target geT d tm d' tm'
                  /\ match_state cd' j' c' m' d' tm')))).
Proof.
intros.
generalize H as MATCH; intro.
apply corestep_ord in H.
destruct H.
{
destruct H as [ef [sig [args AT_EXT]]].
left.
unfold at_external_match.
destruct sim; simpl in *.
clear match_validblocks0 core_diagram0 
  core_initial0 core_halted0 eff_after_external0.
generalize AT_EXT as AT_EXT'; intro.
apply (core_at_external0 cd j c m d tm) in AT_EXT; auto.
destruct AT_EXT as [INJ [targs [VINJ TAT_EXT]]].
exists ef, sig.
generalize (source_safe (S O)); simpl.
rewrite AT_EXT'.
assert (halted source c = None) as ->.
  solve[destruct (at_external_halted_excl source c); try congruence; auto].
intros [x [HP ?]].
exists x, (sig_args sig), args, targs; split; auto.
split; auto.
split; auto.
eapply (P_closed spec_closed); eauto.
apply forall_vals_inject_restrictD in VINJ.
solve[apply forall_inject_val_list_inject; auto].
}
destruct H.
{
destruct H as [rv HALT].
right; left.
unfold halt_match.
destruct sim; simpl in *.
clear match_validblocks0 core_diagram0 
  core_initial0 core_at_external0 eff_after_external0.
generalize HALT as HALT'; intro.
apply (core_halted0 cd j c m d tm) in HALT; auto.
destruct HALT as [rv' [INJ [HALT INJ2]]].
exists rv, rv'.
split; auto.
split; auto.
generalize (source_safe (S O)); simpl; rewrite HALT'.
assert (at_external source c = None) as ->.
  solve[destruct (at_external_halted_excl source c); try congruence; auto].
intros; split; auto.
eapply (exit_closed spec_closed); eauto.
apply inject_restrict; auto.
solve[destruct sim; eapply match_visible0; eauto].
}
{
destruct H as [cd' [j' [c' [m' [STEPN ?]]]]].
destruct H as [H|H].
destruct H as [d' [tm' [TSTEPN MATCH']]].
right; right.
exists cd', j', c', m'.
split; auto.
right; right.
exists d', tm'.
solve[split; auto].
destruct H.
destruct H as [rv [HALT MATCH']].
right; right.
exists cd', j', c', m'.
split; auto.
right.
left.
split; auto.
unfold halt_match.
destruct sim; simpl in *.
clear match_validblocks0 core_diagram0 
  core_initial0 core_at_external0 eff_after_external0.
generalize HALT as HALT'; intro.
apply (core_halted0 cd' j' c' m' d tm) in HALT; auto.
destruct HALT as [rv' [INJ [HALT INJ2]]].
exists rv, rv'.
split; auto.
split; auto.
assert (H: forall n, safeN source spec geS n z c' m').
  intro n. 
  destruct STEPN as [n0 STEPN].
  specialize (source_safe (n + S (S n0))). 
  solve[eapply safe_corestepN_forward in source_safe; eauto].
generalize (H (S O)); simpl; rewrite HALT'.
assert (at_external source c' = None) as ->.
   solve[destruct (at_external_halted_excl source c'); try congruence; auto].
intros; split; auto.
eapply (exit_closed spec_closed); eauto.
apply inject_restrict; auto.
solve[destruct sim; eapply match_visible0; eauto].
destruct H as [ef [sig [args [AT_EXT MATCH']]]].
right; right.
exists cd', j', c', m'.
split; auto.
left.
split; auto.
unfold at_external_match.
destruct sim; simpl in *.
clear match_validblocks0 core_diagram0 
  core_initial0 core_halted0 eff_after_external0.
generalize AT_EXT as AT_EXT'.
apply (core_at_external0 cd' j' c' m' d tm) in AT_EXT; auto.
destruct AT_EXT as [INJ [targs [VINJ TAT_EXT]]].
intros AT_EXT'.
exists ef, sig.
assert (H: forall n, safeN source spec geS n z c' m').
  intro n. 
  destruct STEPN as [n0 STEPN].
  specialize (source_safe (n + S (S n0))). 
  solve[eapply safe_corestepN_forward in source_safe; eauto].
generalize (H (S O)); simpl; rewrite AT_EXT'.
assert (halted source c' = None) as ->.
   solve[destruct (at_external_halted_excl source c'); try congruence; auto].
intros [x]; intros [HP]; intros H2.
exists x, (sig_args sig), args, targs; split; auto.
split; auto.
split; auto.
eapply (P_closed spec_closed); eauto.
apply forall_vals_inject_restrictD in VINJ.
solve[apply forall_inject_val_list_inject; auto].
}
Qed.

End safety_preservation_lemmas.

(** ** Termination preservation *)

Section termination_preservation.
Context  {F V TF TV C D Z data : Type}
         {source : @EffectSem (Genv.t F V) C}
         {target : @EffectSem (Genv.t TF TV) D}
         {geS : Genv.t F V}
         {geT : (Genv.t TF TV)}
         {entry_points : list (val*val*signature)}

  (sim : SM_simulation_inject source target geS geT entry_points)
  (z : Z)
  (c : C)
  (d : D)
  (m : mem)
  (tm: mem)

  (spec : ext_spec Z)
  (spec_closed : injection_closed spec)

  (SRC_DET : corestep_fun source)

  (TGT_DET : corestep_fun target)

  (source_safe : forall n, safeN source spec geS n z c m)
.

Notation data := (sim.(SM_simulation.core_data _ _ _ _ _)).
Notation ord  := (sim.(SM_simulation.core_ord _ _ _ _ _)).
Notation match_state := (sim.(SM_simulation.match_state _ _ _ _ _)).

Lemma termination_preservation:
  forall cd j c' m' rv1,
  match_state cd j c m d tm -> 
  corestep_star source geS c m c' m' -> 
  halted source c' = Some rv1 -> 
  exists d' tm' rv2, 
     corestep_star target geT d tm d' tm' 
  /\ halted target d' = Some rv2.
Proof.
intros.
destruct H0 as [n H0].
revert cd j c m d tm H H0 source_safe.
induction n; intros.
simpl in H0. symmetry in H0; inv H0.
apply (corestep_ord' sim z c d m tm spec) in H; auto.
destruct H.
destruct H as [ef [sig [x [tys [args [targs [A [B [X Y]]]]]]]]].
elimtype False.
solve[destruct (at_external_halted_excl source c); try congruence; auto].
cut (@halt_match F V _ _ C D Z source target spec z c m d tm). intro.
unfold halt_match in H0.
destruct H0 as [rv [trv [? [? [? ?]]]]].
exists d, tm, trv.
split; auto.
solve[exists O; simpl; auto].
destruct H; auto.
destruct H as [? [? [? [? [STEP ?]]]]].
destruct STEP as [n STEP].
simpl in STEP.
destruct STEP as [c2 [m2 [STEP ?]]].
apply corestep_not_halted in STEP.
rewrite STEP in H1; congruence.
simpl in H0.
destruct H0 as [c2 [m2 [? ?]]].
destruct sim; simpl in *.
clear match_validblocks0 core_halted0 
  core_initial0 core_at_external0 eff_after_external0.
generalize H0 as H0'; intro.
eapply core_diagram0 in H0; eauto.
destruct H0 as [d2 [tm2 [cd2 [j2 [? [? [? [? [? [? ?]]]]]]]]]].
assert (SAFE: forall n, safeN source spec geS n z c2 m2). 
  intros n0.
  solve[eapply safe_corestep_forward in H0'; eauto].
specialize (IHn cd2 j2 c2 m2 d2 tm2 H5 H2 SAFE).
destruct IHn as [d' [tm' [trv [? ?]]]].
exists d', tm', trv.
split; auto.
eapply corestep_star_trans; eauto.
destruct H8.
destruct H8 as [n0 H8].
solve[exists (S n0); auto].
destruct H8; auto.
Qed.

End termination_preservation.

Local Open Scope nat_scope.

(** ** Safety & semantics preservation *)

Section safety_preservation.
Variables F V TF TV C D Z : Type.
Variable source : @EffectSem (Genv.t F V) C.
Variable target : @EffectSem (Genv.t TF TV) D.
Variable geS : Genv.t F V.
Variable geT : (Genv.t TF TV).
Variable entry_points : list (val*val*signature).
Variable (SRC_DET : corestep_fun source).
Variable (TGT_DET : corestep_fun target).

Lemma safety_preservation:
  forall sim : SM_simulation_inject source target geS geT entry_points,
    let data := (sim.(SM_simulation.core_data _ _ _ _ _)) in
    let ord  := (sim.(SM_simulation.core_ord _ _ _ _ _)) in
    let match_state := (sim.(SM_simulation.match_state _ _ _ _ _)) in
      forall 
        (c : C)
        (d : D)
        (m : mem)
        (tm: mem)
        (P : val -> mem -> Prop)
        (P_good : forall j v tv m tm, 
                    val_inject j v tv -> Mem.inject j m tm -> P v m -> P tv tm)
        (MATCH : exists (cd: data) (j: SM_Injection), match_state cd j c m d tm)
        (source_safe : forall n, safeN source geS P n c m),
  forall n, safeN target geT P n d tm.
Proof.
intros until n.
destruct MATCH as [cd [j MATCH2]].
revert cd j c m d tm MATCH2 source_safe.
induction n; simpl; auto.
intros.
apply (corestep_ord' sim c d m tm P) in MATCH2; auto.
destruct MATCH2 as [H|H].
destruct H as [rv [rv' [H1 [H2 [H3 H4]]]]].
rewrite H2; auto.
destruct H as [cd' [j' [c' [m' [STEPN [[H1 H2]|H]]]]]].
destruct H2 as [rv [rv' [A1 [A2 [A3 A4]]]]].
rewrite A2; auto.
destruct H as [d' [tm' [TSTEPN MATCH']]].
destruct TSTEPN as [n0 TSTEPN].
cut (halted target d = None). intros ->.
simpl in TSTEPN.
destruct TSTEPN as [d2 [tm2 [TSTEP TSTEPN]]].
exists d2, tm2.
split; auto.
cut (safeN target geT P (n - n0) d' tm'). intro SAFE.
apply (@safe_corestepN_backward _ _ _ _ _ _ _ _ _ _ _ TSTEPN SAFE).
cut (safeN target geT P n d' tm'). intro.
apply safe_downward with (n' := (n - n0)%nat) in H.
apply H. omega.
apply (IHn _ _ _ _ _ _ MATCH').
intros n1.
destruct STEPN as [n2 STEPN].
specialize (source_safe (n1 + S (S n2))).
generalize @safe_corestepN_forward. intro FORW.
solve[apply (FORW _ _ _ _ _ SRC_DET _ _ _ _ _ _ STEPN source_safe)].
simpl in TSTEPN.
destruct TSTEPN as [d2 [tm2 [STEP ?]]].
solve[apply corestep_not_halted in STEP; auto].
Qed.

Lemma halted_safe: 
  forall c m c' m' (P: val -> mem -> Prop) rv, 
  corestep_star source geS c m c' m' -> 
  halted source c' = Some rv -> 
  P rv m' -> 
  (forall n, safeN source geS P n c m).
Proof.
intros.
destruct H as [n0 H].
revert c m H H0.
induction n0.
simpl. intros. inv H.
destruct n; simpl; auto.
solve[rewrite H0; auto].
simpl.
intros c0 m0 [c2 [m2 [STEP STEPN]]] HALTED.
apply (safe_corestep_backward _ _ _ _ _ _ _ _ STEP).
generalize (IHn0 _ _ STEPN HALTED); intros SAFEN.
solve[apply safe_downward with (n1 := n); auto; omega].
Qed.

End safety_preservation.