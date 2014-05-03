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
Require Import sepcomp.wholeprog_simulations.
Require Import sepcomp.closed_safety.
Require Import sepcomp.effect_semantics.

Import Wholeprog_simulation.

Arguments match_state : default implicits.
Arguments core_halted : default implicits.
Arguments core_data : default implicits.
Arguments core_ord : default implicits.
Arguments core_ord_wf : default implicits.
Arguments effcore_diagram : default implicits.

(** * Safety and semantics preservation *)

Section safety_preservation_lemmas.
Context  {F V TF TV C D Z data : Type}
         {source : @EffectSem (Genv.t F V) C}
         {target : @EffectSem (Genv.t TF TV) D}
         {geS : Genv.t F V}
         {geT : Genv.t TF TV}
         (main : val)

  (sim : Wholeprog_simulation source target geS geT main)
  (c : C)
  (d : D)
  (m : mem)
  (tm: mem)

  (P : val -> mem -> Prop)
  (P_good : forall j v tv m tm, val_inject j v tv -> Mem.inject j m tm -> P v m -> P tv tm)

  (SRC_DET : corestep_fun source)

  (TGT_DET : corestep_fun target)
  
  (source_safe : forall n, safeN source geS n c m)
.

Definition my_P := fun (x: core_data sim) => 
   forall j (c : C) (d : D) (m tm : mem),
   (forall n : nat, safeN source geS n c m) ->
   match_state sim x j c m d tm ->
   (exists rv : val, halted source c = Some rv) \/
   (exists (cd' : core_data sim) j' (c' : C) (m' : mem),
      corestep_plus source geS c m c' m' /\
      ((exists (d' : D) (tm' : mem),
          corestep_plus target geT d tm d' tm' /\
          match_state sim cd' j' c' m' d' tm') \/
       (exists rv : val,
        halted source c' = Some rv 
        /\ match_state sim cd' j' c' m' d tm))).

Lemma core_diagram : 
  forall st1 m1 st1' m1', 
    corestep source geS st1 m1 st1' m1' ->
    forall cd st2 mu m2,
      match_state sim cd mu st1 m1 st2 m2 ->
      exists st2', exists m2', exists cd', exists mu',
        match_state sim cd' mu' st1' m1' st2' m2' /\
        ((corestep_plus target geT st2 m2 st2' m2') \/
          corestep_star target geT st2 m2 st2' m2' /\
          core_ord sim cd' cd).
Proof.
intros. apply effax2 in H. destruct H as [M H]. 
exploit effcore_diagram; eauto.
intros [st2' [m2' [cd' [mu' [mtch' [M' [H2 H3]]]]]]].
exists st2',m2',cd',mu'; split; auto. 
destruct H2. left. destruct H1 as [n H1]. 
eapply effstepN_corestepN in H1. solve[exists n; auto].
destruct H1 as [H1 H4]. right; split; auto.
destruct H1 as [n H1]. 
eapply effstepN_corestepN in H1. solve[exists n; auto].
Qed.

Lemma corestep_ord:
  forall cd j,
  match_state sim cd j c m d tm -> 
  (exists rv, halted source c = Some rv) \/
  (exists cd' j' c' m',
      corestep_plus source geS c m c' m'
   /\ ((exists d' tm', corestep_plus target geT d tm d' tm'
                   /\ match_state sim cd' j' c' m' d' tm')
    \/ (exists rv, halted source c' = Some rv 
                   /\ match_state sim cd' j' c' m' d tm))).
Proof.
intros.
revert j c d m tm source_safe H.
assert (my_well_founded_induction
     : (forall x, (forall y, core_ord sim y x -> my_P y) -> my_P x) ->
       forall a, my_P a).
{ apply well_founded_induction; auto. apply (core_ord_wf sim). }
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
eapply core_diagram in STEP; eauto.
destruct STEP as [d2 [tm2 [cd2 [j2 [? H2]]]]].
destruct H2 as [H2|H2]. exists cd2, j2, c2, m2. split; auto.
exists O; simpl; exists c2, m2; split; auto.
solve[left; exists d2, tm2; split; auto].
destruct H2 as [H2 ORD].
specialize (H _ ORD j2 c2 d2 m2 tm2).
assert (SAFE': forall n, safeN source geS n c2 m2).
  solve[intros n; eapply safe_corestep_forward; eauto].
specialize (H SAFE' H0).
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

Definition halt_match c d := 
  exists rv trv, 
    halted source c = Some rv 
    /\ halted target d = Some trv.

Lemma corestep_ord':
  forall cd j,
  match_state sim cd j c m d tm -> 
  halt_match c d
  \/ (exists cd' j' c' m', 
         corestep_plus source geS c m c' m' 
         /\ ((match_state sim cd' j' c' m' d tm /\ halt_match c' d)
            \/ (exists d' tm', 
                  corestep_plus target geT d tm d' tm'
                  /\ match_state sim cd' j' c' m' d' tm'))).
Proof.
intros.
generalize H as MATCH; intro.
apply corestep_ord in H.
destruct H.
{
destruct H as [rv HALT].
left.
unfold halt_match.
generalize HALT as HALT'; intro.
apply (core_halted sim cd j c m d tm) in HALT; auto.
destruct HALT as [j' [rv' [INJ [HALT [INJ2 HLT2]]]]].
exists rv, rv'.
split; auto.
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
generalize HALT as HALT'; intro.
apply (core_halted sim cd' j' c' m' d tm) in HALT; auto.
destruct HALT as [j'' [rv' [INJ [HALT [INJ2 HLT2]]]]].
exists rv, rv'.
split; auto.
}
Qed.

End safety_preservation_lemmas.

Lemma corestepN_splits_lt 
       {G C M} (csem : CoreSemantics G C M) (ge : G)
       c m c' m' c'' m'' n1 n2 :
  corestep_fun csem -> 
  corestepN csem ge (S n1) c m c' m' -> 
  corestepN csem ge n2 c m c'' m'' -> 
  (n1 < n2)%nat -> 
  exists a b,
    (a > O)%nat
    /\ (b=0 -> S n1=n2)%nat
    /\ n2 = plus a b 
    /\ corestepN csem ge a c m c' m'
    /\ corestepN csem ge b c' m' c'' m''.
Proof.
intros FN H1 H2 LT.
revert c m n1 H1 H2 LT.
induction n2; intros.
destruct n1; try inv LT.
destruct n1. 
destruct H1 as [c2' [m2' [STEP STEPN]]].
inv STEPN.
exists (S O), n2.
split; try omega.
split; try omega.
destruct H2 as [c2'' [m2'' [STEP' STEPN']]].
destruct (FN _ _ _ _ _ _ _ STEP STEP').
subst c2'' m2''.
split; auto.
split; auto.
exists c',m'. 
split; simpl; auto.
assert (n1 < n2)%nat by omega.
destruct H1 as [c2 [m2 [STEP STEPN]]].
destruct H2 as [c2' [m2' [STEP' STEPN']]].
assert (c2'=c2 /\ m2=m2') as [? ?].
  { destruct (FN _ _ _ _ _ _ _ STEP STEP').
    subst c2 m2; split; auto. }
subst c2' m2; auto.
destruct (IHn2 c2 m2' n1); auto.
destruct H0 as [n1' [H0 [H1 [H2 [H3 H4]]]]].
exists (S x), n1'.
split; auto.
split. omega.
split; auto. omega.
split; auto.
exists c2,m2'.
split; auto.
Qed.

(** ** Equitermination *)

Definition terminates {G C M} (csem : CoreSemantics G C M) 
    (ge : G) (c : C) (m : M) :=
  exists c' m', corestep_star csem ge c m c' m' 
  /\ exists v, halted csem c' = Some v.

Section equitermination.
Context  {F V TF TV C D Z data : Type}
         {source : @EffectSem (Genv.t F V) C}
         {target : @EffectSem (Genv.t TF TV) D}
         {geS : Genv.t F V}
         {geT : Genv.t TF TV}
         (main : val)

  (sim : Wholeprog_simulation source target geS geT main)

  (SRC_DET : corestep_fun source)

  (TGT_DET : corestep_fun target)
.

Lemma termination_preservation:
  forall cd c m d tm j c' m' rv1
  (source_safe : forall n, safeN source geS n c m),
  match_state sim cd j c m d tm -> 
  corestep_star source geS c m c' m' -> 
  halted source c' = Some rv1 -> 
  terminates target geT d tm.
Proof.
intros.
destruct H0 as [n H0].
revert cd j c m d tm H H0 source_safe.
induction n; intros.
simpl in H0. symmetry in H0; inv H0.
apply (corestep_ord' main sim c d m tm) in H; auto.
cut (@halt_match F V _ _ C D source target c d). intro.
unfold halt_match in H0.
destruct H0 as [rv [trv [? ?]]].
exists d, tm; split; auto. 
solve[exists O; simpl; auto].
solve[exists trv; auto].
destruct H; auto.
destruct H as [? [? [? [? [STEP ?]]]]].
destruct STEP as [n STEP].
simpl in STEP.
destruct STEP as [c2 [m2 [STEP ?]]].
apply corestep_not_halted in STEP.
rewrite STEP in H1; congruence.
simpl in H0.
destruct H0 as [c2 [m2 [? ?]]].
generalize H0 as H0'; intro.
eapply core_diagram in H0; eauto.
destruct H0 as [d2 [tm2 [cd2 [j2 [? ?]]]]].
assert (SAFE: forall n, safeN source geS n c2 m2). 
  intros n0.
  solve[eapply safe_corestep_forward in H0'; eauto].
specialize (IHn cd2 j2 c2 m2 d2 tm2 H0 H2 SAFE).
destruct IHn as [d' [tm' [trv [? ?]]]].
exists d', tm'.
split; auto.
eapply corestep_star_trans; eauto.
destruct H3.
destruct H3 as [n0 H3].
solve[exists (S n0); auto].
destruct H3; auto.
solve[exists x; auto].
Qed.

Lemma termination_reflection:
  forall n c m d tm cd j d' tm' hv'
    (source_safe : forall n, safeN source geS n c m),
    match_state sim cd j c m d tm -> 
    corestepN target geT n d tm d' tm' ->
    halted target d' = Some hv' -> 
    terminates source geS c m.
Proof.
set (my_P := fun (n : nat) => 
   forall (c : C) (m : mem) (d : D) (tm : mem) 
     (cd : core_data sim) (j : StructuredInjections.SM_Injection) 
     (d' : D) (tm' : mem) (hv' : val),
   (forall n0 : nat, safeN source geS n0 c m) ->
   match_state sim cd j c m d tm ->
   corestepN target geT n d tm d' tm' ->
   halted target d' = Some hv' -> terminates source geS c m).
apply (@well_founded_induction _ _ lt_wf my_P); auto.
unfold my_P; clear my_P; intros n IH.

intros c m d tm cd j d' tm' hv' safe MATCH TSTEPN HLT2. 
apply (corestep_ord' main sim c d m tm) in MATCH; auto. 
destruct MATCH as [HLT|H]. 
destruct HLT as [rv [_ [HLT _]]]; exists c,m. split. 
exists O; simpl; auto. solve[exists rv; auto].
destruct H as [cd' [j' [c2 [m2 [STEPN H]]]]]. destruct H as [[H H2]|H].
destruct H2 as [rv [_ [HLT _]]].
destruct STEPN as [n2 STEPN]. 
exists c2,m2. split; auto. exists (S n2); simpl; auto. solve[exists rv; auto].

destruct H as [d2 [tm2 [[n2 TSTEPN2] MTCH2]]].
destruct (lt_dec n2 n) as [pf|pf].
{ assert (TSTEPN': exists n2', (n2' < n)%nat 
    /\ corestepN target geT n2' d2 tm2 d' tm').
  { destruct (corestepN_splits_lt target geT d tm d2 tm2 d' tm' n2 n TGT_DET
              TSTEPN2 TSTEPN pf)
      as [a [b [alt [neq [X [Y U]]]]]].
    exists b; split; auto. omega. }
  destruct TSTEPN' as [n2' [ltpf TSTEPN']].
  assert (safe': forall n, safeN source geS n c2 m2). 
  { destruct STEPN as [q STEPN]. 
    intros n0; eapply safe_corestepN_forward; eauto. }
  destruct (IH n2' ltpf c2 m2 d2 tm2 cd' j' d' tm' hv' safe' MTCH2 TSTEPN' HLT2)
    as [c0 [m0 [[q STEPN1] [hv0 HLT1]]]].
  destruct STEPN as [q' STEPN]. exists c0,m0; split; auto. 
  eapply corestep_star_trans. exists (S q'); eauto. exists q; auto.
  exists hv0; auto. }
{ assert (lt: (n < S n2)%nat) by omega. clear pf.
  destruct n. inv TSTEPN. simpl in TSTEPN2. 
  destruct TSTEPN2 as [? [? [X _]]]; apply corestep_not_halted in X.
  rewrite X in HLT2; congruence.
  destruct (corestepN_splits_lt target geT d tm d' tm' d2 tm2 n (S n2) TGT_DET
              TSTEPN TSTEPN2)
      as [a [b [alt [neq [X [Y W]]]]]]. omega.
  destruct b. rewrite neq in lt; auto. omega. 
  simpl in W. destruct W as [? [? [W _]]].
  apply corestep_not_halted in W; rewrite W in HLT2; congruence. }
Qed.

Lemma equitermination:
  forall cd c m d tm j
  (source_safe : forall n, safeN source geS n c m),
  match_state sim cd j c m d tm -> 
  (terminates source geS c m <-> terminates target geT d tm).
Proof.
intros; split; intros [? [? [A [? B]]]].
eapply termination_preservation; eauto.
destruct A as [n A]; eapply termination_reflection; eauto.
Qed.

End equitermination.

(** ** Safety preservationn *)

Section safety_preservation.
Variables F V TF TV C D : Type.
Variable source : @EffectSem (Genv.t F V) C.
Variable target : @EffectSem (Genv.t TF TV) D.
Variable geS : Genv.t F V.
Variable geT : (Genv.t TF TV).
Variable SRC_DET : corestep_fun source.
Variable TGT_DET : corestep_fun target.
Variable main : val.
 
Lemma safety_preservation:
  forall
  (sim : Wholeprog_simulation source target geS geT main)
  (c : C)
  (d : D)
  (m : mem)
  (tm: mem)
  (MATCH : exists cd j, match_state sim cd j c m d tm)
  (source_safe : forall n, safeN source geS n c m),
  (forall n, safeN target geT n d tm).
Proof.
intros until n.
destruct MATCH as [cd [j MATCH2]].
revert cd j c m d tm MATCH2 source_safe.
induction n; simpl; auto.
intros.
apply (corestep_ord' main sim c d m tm) in MATCH2; auto.
destruct MATCH2 as [H|H].
destruct H as [rv [rv' [H1 H2]]].
rewrite H2; auto.
destruct H as [cd' [j' [c' [m' [STEPN [[H1 H2]|H]]]]]].
destruct H2 as [rv [rv' [A1 A2]]].
rewrite A2; auto.
destruct H as [d' [tm' [TSTEPN MATCH']]].
destruct TSTEPN as [n0 TSTEPN].
cut (halted target d = None). intros ->.
simpl in TSTEPN.
destruct TSTEPN as [d2 [tm2 [TSTEP TSTEPN]]].
exists d2, tm2.
split; auto.
cut (safeN target geT (n - n0) d' tm'). intro SAFE.
apply (@safe_corestepN_backward _ _ _ _ _ _ _ _ _ _ _ TSTEPN SAFE).
cut (safeN target geT n d' tm'). intro.
apply safe_downward with (n' := (n - n0)%nat) in H.
apply H. omega.
apply (IHn _ _ _ _ _ _ MATCH').
intros n1.
destruct STEPN as [n2 STEPN].
specialize (source_safe (n1 + S (S n2))%nat).
generalize @safe_corestepN_forward. intro FORW.
solve[apply (FORW _ _ _ _ _ _ _ _ _ _ _ SRC_DET STEPN source_safe)].
simpl in TSTEPN.
destruct TSTEPN as [d2 [tm2 [STEP ?]]].
solve[apply corestep_not_halted in STEP; auto].
Qed.

Lemma halted_safe: 
  forall c m c' m' rv,
  corestep_star source geS c m c' m' -> 
  halted source c' = Some rv -> 
  (forall n, safeN source geS n c m).
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
apply (safe_corestep_backward STEP).
generalize (IHn0 _ _ STEPN HALTED); intros SAFEN.
solve[apply (safe_downward (n := n)); auto; omega].
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

End safety_preservation.
