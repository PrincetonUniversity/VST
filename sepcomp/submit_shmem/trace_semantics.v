Require Import compcert.lib.Axioms.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Coqlib.
Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Events.

Require Import sepcomp.core_semantics.
Require Import sepcomp.effect_semantics.
Require Import sepcomp.effect_simulations.
Require Import sepcomp.extspec.
Require Import sepcomp.mem_lemmas.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Event.

Record t : Type :=
  mk { pre_mem  : mem
     ; post_mem : mem
     ; args : list val
     ; rv   : option val }.

End Event.

Module TraceSemantics. Section trace_semantics.

Context {G C Z : Type}.

Variable z_init : Z.
Variable sem : @CoopCoreSem G C.
Variable spec : ext_spec Z.

Definition yielded c :=
  (exists ef sig args, at_external sem c = Some (ef, sig, args))
  \/ exists rv, halted sem c = Some rv.

Inductive step
: G -> (Z*list Event.t*C) -> mem -> (Z*list Event.t*C) -> mem -> Prop :=
| trace_step :
  forall ge tr z c m c' m',
  corestep sem ge c m c' m' ->
  step ge (z,tr,c) m (z,tr,c') m'
| trace_extern :
  forall ge tr z c m z' c' m' ef sig args rv x,
  at_external sem c = Some (ef, sig, args) ->
  Mem.unchanged_on (fun b ofs => REACH m (getBlocks args) b=false) m m' ->
  mem_forward m m' ->
  ext_spec_pre spec ef x (sig_args sig) args z m ->
  ext_spec_post spec ef x (sig_res sig) (Some rv) z' m' ->
  after_external sem (Some rv) c = Some c' ->
  step ge (z,tr,c) m (z',Event.mk m m' args (Some rv) :: tr,c') m'.

Definition initial_core (ge : G) (v : val) (vs : list val)
  : option (Z*list Event.t*C) :=
  match initial_core sem ge v vs with
    | Some c => Some (z_init, nil, c)
    | None => None
  end.

Definition halted (c : Z*list Event.t*C) := halted sem (snd c).

Program Definition coresem : CoreSemantics G (Z*list Event.t*C) mem :=
  @Build_CoreSemantics G (Z*list Event.t*C) mem
  initial_core
  (fun _ => None)
  (fun _ _ => None)
  halted
  step
  _ _ _ _.
Next Obligation.
inv H; unfold halted; simpl.
solve[apply corestep_not_halted in H9; auto].
solve[destruct (at_external_halted_excl sem c0); try congruence; auto].
Qed.

Program Definition coopsem : CoopCoreSem G (Z*list Event.t*C) :=
  @Build_CoopCoreSem G (Z*list Event.t*C) coresem _.
Next Obligation.
destruct CS; auto.
solve[apply corestep_fwd in H; auto].
Qed.

Lemma corestep_CORESTEP ge c m c' m' z tr :
  corestep sem ge c m c' m' ->
  corestep coopsem ge (z,tr,c) m (z,tr,c') m'.
Proof. intros; solve[constructor; auto]. Qed.

Lemma corestepN_CORESTEPN ge c m c' m' z tr n :
  corestepN sem ge n c m c' m' ->
  corestepN coopsem ge n (z,tr,c) m (z,tr,c') m'.
Proof.
revert c m; induction n; simpl.
solve[intros ? ?; inversion 1; subst; auto].
intros c m [c2 [m2 [STEP STEPN]]].
exists (z,tr,c2), m2; split.
apply corestep_CORESTEP; auto.
solve[eapply IHn; eauto].
Qed.

Lemma corestepN_splits_lt ge c m c' m' c'' m'' z tr z' tr' n1 n2 :
  corestep_fun sem ->
  corestepN sem ge (S n1) c m c' m' ->
  corestepN coopsem ge n2 (z,tr,c) m (z',tr',c'') m'' ->
  (n1 < n2)%nat ->
  exists a b,
    (a > O)%nat
    /\ n2 = plus a b
    /\ corestepN coopsem ge a (z,tr,c) m (z,tr,c') m'
    /\ corestepN coopsem ge b (z,tr,c') m' (z',tr',c'') m''.
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
inv STEP'.
destruct (FN _ _ _ _ _ _ _ STEP H6).
subst c'0 m2''.
split; auto.
exists (z,tr,c'),m'.
split. constructor; auto. hnf; auto.
apply corestep_not_at_external in STEP.
solve[rewrite STEP in H2; congruence].
assert (n1 < n2)%nat by omega.
destruct H1 as [c2 [m2 [STEP STEPN]]].
destruct H2 as [c2' [m2' [STEP' STEPN']]].
assert (c2'=(z,tr,c2) /\ m2=m2') as [? ?].
  { inv STEP'.
    destruct (FN _ _ _ _ _ _ _ STEP H7).
    subst c2 m2; split; auto.
    apply corestep_not_at_external in STEP.
    rewrite STEP in H3; congruence. }
subst c2' m2; auto.
destruct (IHn2 c2 m2' n1); auto.
destruct H0 as [n1' [H0 [H1 [H2 H3]]]].
exists (S x), n1'.
split; auto.
split. omega.
split; auto.
exists (z,tr,c2),m2'.
split; auto.
Qed.

Lemma corestepN_geq ge c m c' m' c'' m'' z tr z' tr' n1 n2 :
  corestep_fun sem ->
  corestepN sem ge n1 c m c' m' ->
  corestepN coopsem ge n2 (z,tr,c) m (z',tr',c'') m'' ->
  (n1 >= n2)%nat ->
  z=z' /\ tr=tr'.
Proof.
intros FN H1 H2 GEQ.
revert c m n2 H1 H2 GEQ.
induction n1; intros.
destruct n2.
inv H2; auto.
omega.
destruct n2.
inv H2; auto.
destruct H1 as [c2 [m2 [STEP STEPN]]].
destruct H2 as [c2' [m2' [STEP' STEPN']]].
assert (GEQ': (n1 >= n2)%nat) by omega.
assert (c2'=(z,tr,c2) /\ m2=m2') as [? ?].
  { inv STEP'.
    destruct (FN _ _ _ _ _ _ _ STEP H6).
    subst c2 m2; split; auto.
    apply corestep_not_at_external in STEP.
    rewrite STEP in H2; congruence. }
subst c2' m2'.
apply (IHn1 _ _ _ STEPN STEPN'); auto.
Qed.

Lemma yielded_dec c : {yielded c}+{~yielded c}.
Proof.
unfold yielded.
case_eq (at_external sem c).
intros [[ef sig] args] AT.
left. left. exists ef, sig, args. auto.
intros NONE.
case_eq (core_semantics.halted sem c).
intros v HALT.
left. right. exists v. auto.
intros NONE'.
right. intros CONTRA. destruct CONTRA.
destruct H as [? [? [? ?]]]. congruence.
destruct H as [? ?]. congruence.
Qed.

Lemma corestep_nyielded ge c m c' m' :
  corestep sem ge c m c' m' -> ~yielded c.
Proof.
intros STEP NY.
unfold yielded in NY.
destruct NY as [AT|HALT].
destruct AT as [? [? [? AT]]].
apply corestep_not_at_external in STEP.
rewrite STEP in AT; congruence.
destruct HALT as [rv HALT].
apply corestep_not_halted in STEP.
rewrite STEP in HALT; congruence.
Qed.

Lemma nyielded_natext c :
  ~yielded c -> core_semantics.at_external sem c = None.
Proof.
unfold yielded.
case_eq (at_external sem c); auto.
intros [[ef sig] args] AT.
generalize (@at_external_halted_excl _ _ _ sem c).
rewrite AT. intros [|W]; try congruence; auto.
intros CONTRA; elimtype False; apply CONTRA.
left; exists ef, sig, args; auto.
Qed.

Lemma nyielded_nhalted c : ~yielded c -> core_semantics.halted sem c = None.
Proof.
unfold yielded.
case_eq (at_external sem c).
intros [[ef sig] args] AT.
generalize (@at_external_halted_excl _ _ _ sem c).
rewrite AT. intros [|W]; try congruence; auto. intros AT.
case_eq (core_semantics.halted sem c); auto.
intros v HALT.
intros CONTRA; elimtype False; apply CONTRA.
right; exists v; auto.
Qed.

Lemma fun_FUN :
  ExtSpecProperties.det spec ->
  corestep_fun sem ->
  corestep_fun coopsem.
Proof.
intros A B.
unfold corestep_fun.
intros until c''; intros X Y; inv X; inv Y.
destruct (B _ _ _ _ _ _ _ H H7); subst; auto.
apply corestep_not_at_external in H. rewrite H in H3; congruence.
apply corestep_not_at_external in H12. rewrite H12 in H; congruence.
rewrite H8 in H; inv H.
destruct (A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H12 H16 H2 H3)
  as [? [X [? ?]]].
inv X; subst; split; auto.
f_equal; auto.
rewrite H17 in H4; inv H4; auto.
Qed.

End trace_semantics. End TraceSemantics.
