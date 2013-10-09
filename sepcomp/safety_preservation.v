(*CompCert imports*)
Require Import Events.
Require Import Memory.
Require Import Coqlib.
Require Import compcert.common.Values.
Require Import Maps.
Require Import Integers.
Require Import AST.
Require Import Globalenvs.

Require Import Axioms.
Require Import sepcomp.mem_lemmas. (*needed for definition of mem_forward etc*)
Require Import sepcomp.core_semantics.
Require Import sepcomp.forward_simulations.

Import Forward_simulation_inj_exposed.

Section safety.
Context { G C D Z : Type }
        (Hcore : CoreSemantics G C mem )
        (ge : G)
        (P : val -> mem -> Prop).

Fixpoint safeN (n:nat) (c:C) (m:mem) : Prop :=
  match n with
    | O => True
    | S n' => 
      match halted Hcore c with
        | None => 
          exists c', exists m',
            corestep Hcore ge c m c' m' /\
            safeN n' c' m'
        | Some i => val_valid i m /\ P i m
      end
  end.

Definition corestep_fun  :=
  forall ge m q m1 q1 m2 q2 ,
    corestep Hcore ge q m q1 m1 -> 
    corestep Hcore ge q m q2 m2 -> 
    (q1, m1) = (q2, m2).

Lemma safe_downward1 :
  forall n c m,
    safeN (S n) c m -> safeN n c m.
Proof.
  induction n; simpl; intros; auto.
  destruct (halted Hcore c); auto.
  destruct H as [c' [m' [? ?]]].
  exists c', m'; split; auto.
Qed.

Lemma safe_downward : 
  forall (n n' : nat) c m,
    le n' n ->
    safeN n c m -> safeN n' c m.
Proof.
  do 6 intro. revert c m H0. induction H; auto.
  intros. apply IHle. apply safe_downward1. auto.
Qed.

Lemma safe_corestep_forward:
  corestep_fun -> 
  forall c m c' m' n,
    corestep Hcore ge c m c' m' -> safeN (S n) c m -> safeN n c' m'.
Proof.
  simpl; intros.
  erewrite corestep_not_halted in H1; eauto.
  destruct H1 as [c'' [m'' [? ?]]].
  assert ((c',m') = (c'',m'')).
  eapply H; eauto.
  inv H3; auto.
Qed.

Lemma safe_corestepN_forward:
  corestep_fun -> 
  forall c m c' m' n n0,
    corestepN Hcore ge n0 c m c' m' -> safeN (n + S n0) c m -> safeN n c' m'.
Proof.
  intros.
  revert c m c' m' n H0 H1.
  induction n0; intros; auto.
  simpl in H0; inv H0.
  eapply safe_downward in H1; eauto. omega.
  simpl in H0. destruct H0 as [c2 [m2 [STEP STEPN]]].
  apply (IHn0 _ _ _ _ n STEPN). 
  assert (Heq: (n + S (S n0) = S (n + S n0))%nat) by omega.
  rewrite Heq in H1.
  eapply safe_corestep_forward in H1; eauto.
Qed.

Lemma safe_corestep_backward:
  forall c m c' m' n,
    corestep Hcore ge c m c' m' -> safeN (n - 1) c' m' -> safeN n c m.
Proof.
  simpl; intros.
  induction n; simpl; auto.
  erewrite corestep_not_halted; eauto.
  exists c', m'; split; auto.
  assert (Heq: (n = S n - 1)%nat) by omega.
  rewrite Heq; auto.
Qed.

Lemma safe_corestepN_backward:
  forall c m c' m' n n0,
    corestepN Hcore ge n0 c m c' m' -> safeN (n - n0) c' m' -> safeN n c m.
Proof.
  simpl; intros.
  revert c m c' m' n H H0.
  induction n0; intros; auto.
  simpl in H; inv H.
  solve[assert (Heq: (n = n - 0)%nat) by omega; rewrite Heq; auto].
  simpl in H. destruct H as [c2 [m2 [STEP STEPN]]].
  assert (H: safeN (n - 1 - n0) c' m'). 
  eapply safe_downward in H0; eauto. omega.
  specialize (IHn0 _ _ _ _ (n - 1)%nat STEPN H). 
  eapply safe_corestep_backward; eauto.
Qed.

End safety.

Section safety_preservation_lemmas.
Context  {F V G C D Z data : Type}
         {source : CoreSemantics (Genv.t F V) C mem}
         {target : CoreSemantics G D mem}
         {match_state : data -> meminj -> C -> mem -> D -> mem -> Prop}
         {ord : data -> data -> Prop}
         {geS : Genv.t F V}
         {geT : G}
         {entry_points : list (val*val*signature)}

  (sim : Forward_simulation_inject source target geS geT entry_points data match_state ord)
  (c : C)
  (d : D)
  (m : mem)
  (tm: mem)

  (P : val -> mem -> Prop)
  (P_good : forall j v tv m tm, val_inject j v tv -> Mem.inject j m tm -> P v m -> P tv tm)

  (SRC_DET : corestep_fun source)

  (TGT_DET : corestep_fun target)
  
  (source_safe : forall n, safeN source geS P n c m)
.

Definition my_P := fun (x: data) => 
   forall (j : meminj) (c : C) (d : D) (m tm : mem),
   (forall n : nat, safeN source geS P n c m) ->
   match_state x j c m d tm ->
   (exists rv : val, halted source c = Some rv) \/
   (exists (cd' : data) (j' : meminj) (c' : C) (m' : mem),
      corestep_plus source geS c m c' m' /\
      ((exists (d' : D) (tm' : mem),
          corestep_plus target geT d tm d' tm' /\
          match_state cd' j' c' m' d' tm') \/
       (exists rv : val,
          halted source c' = Some rv /\ match_state cd' j' c' m' d tm))).

Lemma corestep_ord:
  forall cd j,
  match_state cd j c m d tm -> 
  (exists rv, halted source c = Some rv) \/
  (exists cd' j' c' m',
      corestep_plus source geS c m c' m'
   /\ ((exists d' tm', corestep_plus target geT d tm d' tm'
                   /\ match_state cd' j' c' m' d' tm')
    \/ (exists rv, halted source c' = Some rv 
                   /\ match_state cd' j' c' m' d tm))).
Proof.
destruct sim.
clear match_memwd0 match_validblocks0 core_halted0 
  core_initial0 core_at_external0 core_after_external0.
intros.
revert j c d m tm source_safe H.
assert (my_well_founded_induction
     : (forall x, (forall y, ord y x -> my_P y) -> my_P x) ->
       forall a, my_P a).
  solve[apply well_founded_induction; auto].
unfold my_P in my_well_founded_induction.
apply my_well_founded_induction; auto.
intros.
case_eq (halted source c).
intros.
solve[left; exists v; auto].
intros HALTED_NONE.
right.
generalize H0 as SAFE; intro.
specialize (H0 (S O)); simpl in H0.
rewrite HALTED_NONE in H0.
destruct H0 as [c2 [m2 [STEP _]]].
generalize STEP as STEP'; intro.
eapply core_diagram0 in STEP; eauto.
destruct STEP as [d2 [tm2 [cd2 [j2 [? [? [? H2]]]]]]].
destruct H2.
exists cd2, j2, c2, m2.
split; auto.
exists O; simpl; exists c2, m2; split; auto.
solve[left; exists d2, tm2; split; auto].
destruct H2 as [H2 ORD].
specialize (H _ ORD j2 c2 d2 m2 tm2).
assert (SAFE': forall n, safeN source geS P n c2 m2).
  solve[intros n; eapply safe_corestep_forward; eauto].
specialize (H SAFE' H4).
destruct H2 as [n H2].
destruct n. inv H2.
destruct H.
destruct H as [rv HALTED].
exists cd2, j2, c2, m2.
split; auto.
solve[exists O; simpl; exists c2, m2; split; auto].
solve[right; exists rv; split; auto].
destruct H as [cd' [j' [c' [m' [STEPN H]]]]].
destruct H as [H|H].
destruct H as [d' [tm' [TSTEP' MATCH']]].
exists cd', j', c', m'.
split; auto. 
destruct STEPN as [n STEPN].
exists (S n).
simpl.
exists c2, m2.
split; auto.
solve[left; exists d', tm'; split; auto].
destruct H as [rv [HALT MATCH']].
exists cd', j', c', m'.
split; auto. 
destruct STEPN as [n STEPN].
exists (S n).
simpl.
exists c2, m2.
split; auto.
solve[right; exists rv; split; auto].
exists cd2, j2, c2, m2.
split; auto. 
solve[exists O; simpl; exists c2, m2; split; auto].
left. 
exists d2, tm2.
split; auto.
exists n; auto.
Qed.

Definition halt_match c m d tm := 
  exists rv trv, 
    halted source c = Some rv 
    /\ halted target d = Some trv
    /\ P rv m 
    /\ P trv tm
    /\ val_valid trv tm.

Lemma corestep_ord':
  forall cd j,
  match_state cd j c m d tm -> 
  halt_match c m d tm
  \/ (exists cd' j' c' m', 
         corestep_plus source geS c m c' m' 
         /\ ((match_state cd' j' c' m' d tm /\ halt_match c' m' d tm)
            \/ (exists d' tm', 
                  corestep_plus target geT d tm d' tm'
                  /\ match_state cd' j' c' m' d' tm'))).
Proof.
intros.
generalize H as MATCH; intro.
apply corestep_ord in H.
destruct H.
destruct H as [rv HALT].
left.
unfold halt_match.
destruct sim.
clear match_memwd0 match_validblocks0 core_diagram0 
  core_initial0 core_at_external0 core_after_external0.
generalize HALT as HALT'; intro.
apply (core_halted0 cd j c m d tm) in HALT; auto.
destruct HALT as [rv' [INJ [HALT [INJ2 VAL]]]].
exists rv, rv'.
split; auto.
split; auto.
specialize (source_safe (S O)).
simpl in source_safe.
rewrite HALT' in source_safe.
destruct source_safe.
split; auto.
split; auto.
eapply P_good; eauto.
specialize (source_safe (S O)).
simpl in source_safe.
rewrite HALT' in source_safe.
solve[destruct source_safe; auto].
destruct H as [cd' [j' [c' [m' [STEPN ?]]]]].
destruct H as [H|H].
destruct H as [d' [tm' [TSTEPN MATCH']]].
right.
exists cd', j', c', m'.
split; auto.
right.
exists d', tm'.
solve[split; auto].
destruct H as [rv [HALT MATCH']].
right.
exists cd', j', c', m'.
split; auto.
left.
split; auto.
unfold halt_match.
destruct sim.
clear match_memwd0 match_validblocks0 core_diagram0 
  core_initial0 core_at_external0 core_after_external0.
generalize HALT as HALT'; intro.
apply (core_halted0 cd' j' c' m' d tm) in HALT; auto.
destruct HALT as [rv' [INJ [HALT [INJ2 VAL]]]].
exists rv, rv'.
split; auto.
split; auto.
assert (H: forall n, safeN source geS P n c' m').
  intro n. 
  destruct STEPN as [n0 STEPN].
  specialize (source_safe (n + S (S n0))). 
  solve[eapply safe_corestepN_forward in source_safe; eauto].
specialize (H (S O)).
simpl in H.
rewrite HALT' in H.
destruct H.
split; auto.
split; auto.
eapply P_good; eauto.
assert (H: forall n, safeN source geS P n c' m').
  intro n. 
  destruct STEPN as [n0 STEPN].
  specialize (source_safe (n + S (S n0))). 
  solve[eapply safe_corestepN_forward in source_safe; eauto].
specialize (H (S O)).
simpl in H.
rewrite HALT' in H.
destruct H; auto.
Qed.

End safety_preservation_lemmas.

Section safety_preservation.
Variables F V G C D Z data : Type.

Variable source : CoreSemantics (Genv.t F V) C mem.

Variable target : CoreSemantics G D mem.

Variable match_state : data -> meminj -> C -> mem -> D -> mem -> Prop.

Variable ord : data -> data -> Prop.

Variable geS : Genv.t F V.
Variable geT : G.

Variable entry_points : list (val*val*signature).

Variables
  (sim : Forward_simulation_inject source target geS geT entry_points data match_state ord)
  (c : C)
  (d : D)
  (m : mem)
  (tm: mem)

  (P : val -> mem -> Prop)
  (P_good : forall j v tv m tm, val_inject j v tv -> Mem.inject j m tm -> P v m -> P tv tm)

  (MATCH : exists (cd: data) (j: meminj), match_state cd j c m d tm)

  (NEVER_EXTERNAL : forall d, at_external target d = None)

  (SRC_DET : corestep_fun source)

  (TGT_DET : corestep_fun target)
  
  (source_safe : forall n, safeN source geS P n c m)
.

Lemma safety_preservation_less_extcalls:
  forall n, safeN target geT P n d tm.
Proof.
intros n.
destruct MATCH as [cd [j MATCH2]].
clear MATCH; revert cd j c m d tm MATCH2 source_safe.
induction n; simpl; auto.
intros.
apply (corestep_ord' sim c d m tm P) in MATCH2; auto.
destruct MATCH2 as [H|H].
destruct H as [rv [rv' [H1 [H2 [H3 H4]]]]].
rewrite H2. destruct H4.
split; auto.
destruct H as [cd' [j' [c' [m' [STEPN [[H1 H2]|H]]]]]].
destruct H2 as [rv [rv' [A1 [A2 [A3 A4]]]]].
rewrite A2.
destruct A4.
split; auto.
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

End safety_preservation.