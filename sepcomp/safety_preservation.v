(*CompCert imports*)
Require Import Events.
Require Import Memory.
Require Import Coqlib.
Require Import compcert.common.Values.
Require Import Maps.
Require Import Integers.
Require Import AST.
Require Import Globalenvs.

Require Import msl.Axioms.
Require Import sepcomp.mem_lemmas. (*needed for definition of mem_forward etc*)
Require Import sepcomp.core_semantics.
Require Import sepcomp.core_semantics_lemmas.
Require Import sepcomp.forward_simulations.

Import Forward_simulation_inj_exposed.

(** * Safety and semantics preservation *)

(** ** Definition of safety w/r/t predicate P *)

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
        | Some i => P i m
      end
  end.

Definition corestep_fun  :=
  forall ge m q m1 q1 m2 q2 ,
    corestep Hcore ge q m q1 m1 -> 
    corestep Hcore ge q m q2 m2 -> 
    (q1, m1) = (q2, m2).


Lemma corestep_star_fun : 
  corestep_fun -> 
  forall c m c' m' c'' m'' n,
  corestepN Hcore ge n c m c' m' -> 
  corestepN Hcore ge n c m c'' m'' -> 
  c'=c'' /\ m'=m''.
Proof.
intro FUN. intros. revert c m H H0. induction n; auto.
simpl. intros ? ?. inversion 1; subst. inversion 1; subst. 
split; auto.
simpl.
intros c m H H2.
destruct H as [c2 [m2 [STEP STEPN]]].
destruct H2 as [c2' [m2' [STEP' STEPN']]].
assert ((c2,m2)=(c2',m2')).
  unfold corestep_fun in FUN.
  eapply FUN; eauto.
inv H.
eapply IHn; eauto.
Qed.

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
Context  {F V TF TV C D Z data : Type}
         {source : CoreSemantics (Genv.t F V) C mem}
         {target : CoreSemantics (Genv.t TF TV) D mem}
         {match_state : data -> meminj -> C -> mem -> D -> mem -> Prop}
         {ord : data -> data -> Prop}
         {geS : Genv.t F V}
         {geT : Genv.t TF TV}
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
clear match_validblocks0 core_halted0 
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
    /\ P trv tm.

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
{
destruct H as [rv HALT].
left.
unfold halt_match.
destruct sim.
clear match_validblocks0 core_diagram0 
  core_initial0 core_at_external0 core_after_external0.
generalize HALT as HALT'; intro.
apply (core_halted0 cd j c m d tm) in HALT; auto.
destruct HALT as [rv' [INJ [HALT INJ2]]].
exists rv, rv'.
split; auto.
split; auto.
specialize (source_safe (S O)).
simpl in source_safe.
rewrite HALT' in source_safe.
split; auto.
eapply P_good; eauto.
}
{
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
clear match_validblocks0 core_diagram0 
  core_initial0 core_at_external0 core_after_external0.
generalize HALT as HALT'; intro.
apply (core_halted0 cd' j' c' m' d tm) in HALT; auto.
destruct HALT as [rv' [INJ [HALT INJ2]]].
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
split; auto.
eapply P_good; eauto.
}
Qed.

End safety_preservation_lemmas.

(** ** Termination preservation *)

Section termination_preservation.
Context  {F V TF TV C D Z data : Type}
         {source : CoreSemantics (Genv.t F V) C mem}
         {target : CoreSemantics (Genv.t TF TV) D mem}
         {match_state : data -> meminj -> C -> mem -> D -> mem -> Prop}
         {ord : data -> data -> Prop}
         {geS : Genv.t F V}
         {geT : (Genv.t TF TV)}
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
apply (corestep_ord' sim c d m tm P) in H; auto.
cut (@halt_match F V _ _ C D source target P c m d tm). intro.
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
destruct sim.
clear match_validblocks0 core_halted0 
  core_initial0 core_at_external0 core_after_external0.
generalize H0 as H0'; intro.
eapply core_diagram0 in H0; eauto.
destruct H0 as [d2 [tm2 [cd2 [j2 [? [? [? ?]]]]]]].
assert (SAFE: forall n, safeN source geS P n c2 m2). 
  intros n0.
  solve[eapply safe_corestep_forward in H0'; eauto].
specialize (IHn cd2 j2 c2 m2 d2 tm2 H4 H2 SAFE).
destruct IHn as [d' [tm' [trv [? ?]]]].
exists d', tm', trv.
split; auto.
eapply corestep_star_trans; eauto.
destruct H5.
destruct H5 as [n0 H5].
solve[exists (S n0); auto].
destruct H5; auto.
Qed.

End termination_preservation.

Local Open Scope nat_scope.

(** ** Safety & semantics preservation *)

Section safety_preservation.
Variables F V TF TV C D Z data : Type.
Variable source : CoreSemantics (Genv.t F V) C mem.
Variable target : CoreSemantics (Genv.t TF TV) D mem.
Variable match_state : data -> meminj -> C -> mem -> D -> mem -> Prop.
Variable ord : data -> data -> Prop.
Variable geS : Genv.t F V.
Variable geT : (Genv.t TF TV).
Variable entry_points : list (val*val*signature).
Variable (SRC_DET : corestep_fun source).
Variable (TGT_DET : corestep_fun target).

Lemma safety_preservation:
  forall
  (sim : Forward_simulation_inject source target geS geT entry_points data match_state ord)
  (c : C)
  (d : D)
  (m : mem)
  (tm: mem)

  (P : val -> mem -> Prop)
  (P_good : forall j v tv m tm, val_inject j v tv -> Mem.inject j m tm -> P v m -> P tv tm)
  (MATCH : exists (cd: data) (j: meminj), match_state cd j c m d tm)
  (source_safe : forall n, safeN source geS P n c m),

  (forall n, safeN target geT P n d tm).
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

Lemma safely_halted d tm d' tm' P rv n :
  (forall n, safeN target geT P n d tm) -> 
  corestepN target geT n d tm d' tm' -> 
  halted target d' = Some rv -> 
  P rv tm'.
Proof.
revert d tm; induction n.
intros d tm ?. inversion 1; subst. intros HALT.
generalize (H (S O)); simpl.
rewrite HALT; auto.
intros.
destruct H0 as [d2 [tm2 [H2 H3]]].
apply IHn with (d := d2) (tm := tm2); auto.
intros n0; apply safe_corestep_forward with (c := d) (m := tm); auto.
Qed.

Lemma halted_same_num_steps d tm d' tm' d'' tm'' rv rv' n n' :
  corestepN target geT n d tm d' tm' -> 
  corestepN target geT n' d tm d'' tm'' -> 
  halted target d' = Some rv -> 
  halted target d'' = Some rv' -> 
  n=n'.
Proof.
revert d tm n'; induction n.
intros d tm. simpl. inversion 1; subst. 
destruct n'. simpl. inversion 1; subst; auto.
simpl. intros [d2 [m2 [STEP STEP']]] HALT HALT'.
apply corestep_not_halted in STEP.
rewrite HALT in STEP; congruence.
intros.
destruct H as [d2 [tm2 [H H']]].
destruct n'.
simpl in H0. inv H0. 
apply corestep_not_halted in H.
rewrite H2 in H; congruence.
erewrite IHn; eauto.
destruct H0 as [d2' [tm2' [? ?]]].
generalize (TGT_DET _ _ _ _ _ _ _ H H0).
inversion 1; subst; auto.
Qed.

Lemma semantics_preservation:
  forall c m d tm c' m' rv (P: val -> mem -> Prop) cd j,
  Forward_simulation_inject source target geS geT entry_points data match_state ord -> 
  (forall j v tv m tm, val_inject j v tv -> Mem.inject j m tm -> P v m -> P tv tm) -> 
  corestep_star source geS c m c' m' -> 
  halted source c' = Some rv -> 
  P rv m' -> 
  match_state cd j c m d tm -> 
  (exists d' tm' rv', corestep_star target geT d tm d' tm'
    /\ halted target d' = Some rv' 
    /\ P rv' tm') /\
  (forall d' tm' rv', 
    corestep_star target geT d tm d' tm' ->
    halted target d' = Some rv' ->
    P rv' tm').
Proof.
intros until j; intros sim P_good H1 H2 H3 H4.
generalize (halted_safe _ _ _ _ _ _ H1 H2 H3); intros safe.
generalize H2 as H2'; intro.
eapply termination_preservation in H2; eauto.
destruct H2 as [d' [tm' [rv2 [[n H] H0]]]].
generalize (safety_preservation sim c d m tm _ P_good); intro SAFE.
assert (A: 
  exists (d'0 : D) (tm'0 : mem) (rv' : val),
    corestep_star target geT d tm d'0 tm'0 /\
    halted target d'0 = Some rv' /\ P rv' tm'0).
{ exists d', tm', rv2; split; auto. exists n; auto. split; auto.
  apply safely_halted 
    with (d := d) (tm := tm) (tm' := tm') (P := P) (n := n) in H0; auto.
  eauto. }
split; auto.
intros d'' tm'' rv'' TSTEPN THALT.
assert (rv''=rv2 /\ tm''=tm') as [-> ->]. 
{ generalize (@corestep_star_fun _ _ target geT TGT_DET
              d tm d' tm' d'' tm'').
  intros B.
  destruct TSTEPN as [n0 TSTEPN].
  generalize H as H'.
  eapply halted_same_num_steps in H; eauto.
  intros; subst n0; apply B in TSTEPN; auto.
  destruct TSTEPN as [? ?]; subst.
  rewrite H0 in THALT; inv THALT; auto. }
apply safely_halted 
  with (d := d) (tm := tm) (tm' := tm') (P := P) (n := n) in H0; auto.
eauto.
Qed.

(*
Print Assumptions semantics_preservation.
Section Variables:
C : Type
D : Type
F : Type
SRC_DET : corestep_fun source
TF : Type
TGT_DET : corestep_fun target
TV : Type
V : Type
data : Type
entry_points : list (val * val * signature)
geS : Genv.t F V
geT : Genv.t TF TV
match_state : data -> meminj -> C -> mem -> D -> mem -> Prop
ord : data -> data -> Prop
source : CoreSemantics (Genv.t F V) C mem
target : CoreSemantics (Genv.t TF TV) D mem
*)

End safety_preservation.
