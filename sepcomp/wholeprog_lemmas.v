Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Axioms.

Require Import compcert.common.Events.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.

Require Import VST.sepcomp.mem_lemmas.
Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.sepcomp.wholeprog_simulations.
Require Import VST.sepcomp.closed_safety.
Require Import VST.sepcomp.effect_semantics.

(*
Import Wholeprog_sim.

Arguments match_state : default implicits.
Arguments core_halted : default implicits.
Arguments core_data : default implicits.
Arguments core_ord : default implicits.
Arguments core_ord_wf : default implicits.
Arguments core_diagram : default implicits.

(** * Safety and semantics preservation *)

Section safety_preservation_lemmas.
Context  {G TG C D M TM Z data : Type}
         {source : @CoreSemantics G C M}
         {target : @CoreSemantics TG D TM}
         {geS : G}
         {geT : TG}
         {ge_inv : G -> TG -> Prop}
         {init_inv : meminj -> G -> list val -> M -> TG -> list val -> TM -> Prop}
         {halt_inv : meminj (*structured_injections.SM_Injection*) ->
                     G -> val -> M -> TG -> val -> TM -> Prop}
         (main : val)

  (sim : Wholeprog_sim source target geS geT main ge_inv init_inv halt_inv)
  (c : C)
  (d : D)
  (m : M)
  (tm: TM)

  (TGT_DET : corestep_fun target)

  (source_safe : forall n, safeN source geS n c m).

Definition my_P := fun (x: core_data sim) =>
   forall j (c : C) (d : D) (m : M) (tm : TM),
   (forall n : nat, safeN source geS n c m) ->
   match_state sim x j c m d tm ->
   (exists rv : val, halted source c = Some rv) \/
   (exists (cd' : core_data sim) j' (c' : C) (m' : M),
      corestep_plus source geS c m c' m' /\
      ((exists (d' : D) (tm' : TM),
          corestep_plus target geT d tm d' tm' /\
          match_state sim cd' j' c' m' d' tm') \/
       (exists rv : val,
        halted source c' = Some rv
        /\ match_state sim cd' j' c' m' d tm))).

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
destruct H0 as [H0 HALL].
destruct H0 as [c2 [m2 STEP]].
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
destruct HALT as [j' [rv' [INJ HALT]]].
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
destruct HALT as [j'' [rv' [INJ HALT]]].
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

Section termination_preservation.
Context  {G TG C D M TM Z data : Type}
         {source : @CoreSemantics G C M}
         {target : @CoreSemantics TG D TM}
         {geS : G}
         {geT : TG}
         {ge_inv : G -> TG -> Prop}
         {init_inv : meminj -> G -> list val -> M -> TG -> list val -> TM -> Prop}
         {halt_inv : meminj (*structured_injections.SM_Injection *)->
                     G -> val -> M -> TG -> val -> TM -> Prop}
         (main : val)

  (sim : Wholeprog_sim source target geS geT main ge_inv init_inv halt_inv).

Lemma termination_preservation:
  forall cd c m d tm j c' m' rv1,
  match_state sim cd j c m d tm ->
  corestep_star source geS c m c' m' ->
  halted source c' = Some rv1 ->
  terminates target geT d tm.
Proof.
intros.
destruct H0 as [n H0].
revert cd j c m d tm H H0.
induction n; intros.
simpl in H0. symmetry in H0; inv H0.
cut (@halt_match G _ C D _ _ source target c d). intro.
unfold halt_match in H0.
destruct H0 as [rv [trv [? ?]]].
exists d, tm; split; auto.
solve[exists O; simpl; auto].
solve[exists trv; auto].
generalize H1 as H1'; intro.
eapply core_halted in H1; eauto.
destruct H1 as [? [rv2 [? ?]]].
exists rv1, rv2; split; auto.
simpl in H0.
destruct H0 as [c2 [m2 [STEP STEPN]]].
generalize STEP as STEP'; intro.
apply corestep_not_halted in STEP.
eapply core_diagram in STEP'; eauto.
destruct STEP' as [? [? [cd' [j' [MATCH ?]]]]].
clear H.
destruct H0 as [X|[X Y]].
eapply IHn in MATCH; eauto.
unfold terminates in MATCH|-*.
destruct MATCH as [x' [tm' [Y [v W]]]].
exists x', tm'; split; eauto.
eapply corestep_star_trans; eauto.
solve[eapply corestep_plus_star; eauto].
eapply IHn in MATCH; eauto.
unfold terminates in MATCH|-*.
destruct MATCH as [x' [tm' [U [v W]]]].
exists x', tm'; split; eauto.
solve[eapply corestep_star_trans; eauto].
Qed.

End termination_preservation.

Section equitermination.
Context  {G TG C D M TM Z data : Type}
         {source : @CoreSemantics G C M}
         {target : @CoreSemantics TG D TM}
         {geS : G}
         {geT : TG}
         {ge_inv : G -> TG -> Prop}
         {init_inv : meminj -> G -> list val -> M -> TG -> list val -> TM -> Prop}
         {halt_inv : meminj (*structured_injections.SM_Injection*) ->
                     G -> val -> M -> TG -> val -> TM -> Prop}
         (main : val)

  (sim : Wholeprog_sim source target geS geT main ge_inv init_inv halt_inv)
  (TGT_DET : corestep_fun target).

Lemma termination_reflection:
  forall n c m d tm cd j d' tm' hv'
    (source_safe : forall n, safeN source geS n c m),
    match_state sim cd j c m d tm ->
    corestepN target geT n d tm d' tm' ->
    halted target d' = Some hv' ->
    terminates source geS c m.
Proof.
set (my_P := fun (n : nat) =>
   forall (c : C) (m : M) (d : D) (tm : TM)
     (cd : core_data sim) (j : meminj (*structured_injections.SM_Injection*))
     (d' : D) (tm' : TM) (hv' : val),
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
*)