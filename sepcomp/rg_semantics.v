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

Require Import sepcomp.mem_lemmas.
Require Import core_semantics.

(** Rely-Guarantee core semantics extend coop core semantics with a predicate 
   tracking blocks "private" to this core.  Inuitively, private blocks are 
   blocks allocated by coresteps of this semantics. *)

Record RelyGuaranteeSemantics {G C} :=
  { csem :> CoopCoreSem G C;
    private_block: C -> block -> Prop;
    private_dec: forall c b, 
      {private_block c b}+{~private_block c b};
    private_initial: forall b ge v vs c,
      initial_core csem ge v vs = Some c -> 
      ~private_block c b;
    private_step: forall b ge c m c' m',
      corestep csem ge c m c' m' -> 
      private_block c' b ->
      private_block c b \/ (Mem.nextblock m <= b < Mem.nextblock m')%positive;
    private_external: forall b c c' retv ef sig args,
      at_external csem c = Some (ef, sig, args) -> 
      after_external csem retv c = Some c' -> 
      private_block c' b -> private_block c b }.

Implicit Arguments RelyGuaranteeSemantics [].

Record EqRelyGuaranteeSemantics {G C} :=
  { eq_csem :> CoopCoreSem G C;
    eq_private_block: C -> block -> Prop;
    eq_private_dec: forall c b, 
      {eq_private_block c b}+{~eq_private_block c b};
    eq_private_initial: forall b ge v vs c,
      initial_core eq_csem ge v vs = Some c -> 
      ~eq_private_block c b;
    eq_private_step: forall b ge c m c' m',
      corestep eq_csem ge c m c' m' -> 
      (eq_private_block c' b <->
       eq_private_block c b \/ (Mem.nextblock m <= b < Mem.nextblock m')%positive);
    eq_private_external: forall b c c' retv ef sig args,
      at_external eq_csem c = Some (ef, sig, args) -> 
      after_external eq_csem retv c = Some c' -> 
      (eq_private_block c' b <-> eq_private_block c b) }.

Implicit Arguments EqRelyGuaranteeSemantics [].

Program Definition eq_rely2rely_sem G C 
  (eq_rgsem: EqRelyGuaranteeSemantics G C): RelyGuaranteeSemantics G C :=
 {| csem := eq_csem eq_rgsem;
    private_block := eq_private_block eq_rgsem;
    private_dec := eq_private_dec eq_rgsem;
    private_initial := _;
    private_step := _;
    private_external := _ |}.
Next Obligation. eapply (eq_private_initial eq_rgsem) in H; eauto. Qed.
Next Obligation. eapply (eq_private_step eq_rgsem); eauto. Qed.
Next Obligation. erewrite <-(eq_private_external eq_rgsem); eauto. Qed.

Section RelyGuaranteeSemanticsLemmas.
Context {G C: Type}.
Variable rgsem: RelyGuaranteeSemantics G C.

Lemma private_new: forall b ge c m c' m',
  ~private_block rgsem c b -> 
  corestep rgsem ge c m c' m' -> 
  private_block rgsem c' b -> 
  (Mem.nextblock m <= b < Mem.nextblock m')%positive.
Proof.
intros until m'; intros H1 H2 H3.
apply (private_step _ b) in H2; auto.
destruct H2; auto.
elimtype False; auto.
Qed.

Lemma private_newN: forall b ge n c m c' m',
  ~private_block rgsem c b -> 
  corestepN rgsem ge n c m c' m' -> 
  private_block rgsem c' b -> 
  (Mem.nextblock m <= b < Mem.nextblock m')%positive. 
Proof.
intros until m'; revert c m; induction n; auto.
intros c m H1 H2 H3.
simpl in H2.
inv H2.
solve[elimtype False; auto].
intros c m H1 H2 H3.
simpl in H2.
destruct H2 as [c2 [m2 [STEP STEPN]]].
destruct (private_dec rgsem c2 b).
apply (private_new b) in STEP; auto.
apply corestepN_fwd in STEPN.
apply forward_nextblock in STEPN.
xomega.
cut ((Mem.nextblock m2 <= b < Mem.nextblock m')%positive). intro H4.
apply corestep_fwd in STEP.
apply forward_nextblock in STEP.
xomega.
solve[eapply IHn with (m := m2); eauto].
Qed.
Lemma mem_unchanged_unmapped_trans: 
  forall m1 m1' m2 m3 f1 f2 c
  (Fwd12: mem_forward m1 m2) (Fwd23: mem_forward m2 m3), 
  Mem.unchanged_on (fun b ofs => 
    loc_unmapped f1 b ofs /\ private_block rgsem c b) m1 m2 ->
  inject_separated f1 f2 m1 m1' ->
  Mem.unchanged_on (fun b ofs => 
    loc_unmapped f2 b ofs /\ private_block rgsem c b) m2 m3 ->
  Mem.unchanged_on (fun b ofs => 
    loc_unmapped f1 b ofs /\ private_block rgsem c b) m1 m3.
Proof.
  intros until c; intros Fwd12 Fwd23 UNCH1 SEP UNCH2.
  destruct UNCH1 as [PERMS1 LOADS1].
  destruct UNCH2 as [PERMS2 LOADS2].
  assert (UNMAPPED: forall b ofs,
      loc_unmapped f1 b ofs -> Mem.valid_block m1 b -> loc_unmapped f2 b ofs).
    unfold loc_unmapped; intros.
    destruct (f2 b) as [[b' delta] |]eqn:?; auto.
    exploit SEP; eauto. tauto.
  intros; split; intros.
  (* perms *)
  split; intros.
    specialize (PERMS1 _ _ k p H H0).
    rewrite PERMS1 in H1.
    apply PERMS2.
    destruct H as [? ?]. split; auto.
    apply Fwd12. apply H0.
    assumption.
  rewrite PERMS1; trivial. 
  rewrite PERMS2; trivial.
    destruct H as [? ?]. split; auto. 
  apply Fwd12. apply H0. 
  (* loads *)
  rewrite LOADS2. 
    apply LOADS1; auto.
    intros. 
     destruct H as [? ?]. split; auto. 
      apply UNMAPPED; auto. eauto with mem.
    apply PERMS1; eauto with mem.
Qed.

Lemma unchanged_outofreach_trans: 
  forall m1 m2 m1' m2' m3' f1 f2 c
  (Fwd12: mem_forward m1' m2') (Fwd23: mem_forward m2' m3'),
  Mem.inject f1 m1 m1' ->
  Mem.inject f2 m2 m2' ->
  Mem.unchanged_on (fun b ofs => 
    loc_out_of_reach f1 m1 b ofs /\ private_block rgsem c b) m1' m2' ->
  inject_separated f1 f2 m1 m1' ->
  (forall b ofs p, Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p ->
    Mem.perm m1 b ofs Max p) ->
  inject_incr f1 f2 ->
  Mem.unchanged_on (fun b ofs => 
    loc_out_of_reach f2 m2 b ofs /\ private_block rgsem c b) m2' m3' ->
  Mem.unchanged_on (fun b ofs => 
    loc_out_of_reach f1 m1 b ofs /\ private_block rgsem c b) m1' m3'.
Proof.
  intros until c; intros Fwd12 Fwd23 INJ1 INJ2 UNCH1 SEP MAXPERMS INCR UNCH2.
  destruct UNCH1 as [PERMS1 LOADS1].
  destruct UNCH2 as [PERMS2 LOADS2].
  assert (OUTOFREACH: forall b ofs k p,
      loc_out_of_reach f1 m1 b ofs ->
      Mem.perm m1' b ofs k p ->
      loc_out_of_reach f2 m2 b ofs).
    unfold loc_out_of_reach; intros.
    destruct (f1 b0) as [[b' delta'] |]eqn:?.
    exploit INCR; eauto. intros EQ; rewrite H1 in EQ; inv EQ.
    red; intros. eelim H; eauto. eapply MAXPERMS; eauto.
    eapply Mem.valid_block_inject_1 with (f := f1); eauto.
    exploit SEP; eauto. intros [A B]. elim B; eauto with mem.
  intros; split; intros.
  (* perms *)
  split; intros.
    specialize (PERMS1 _ _ k p H H0).
    apply PERMS2.
    destruct H as [? ?]. split; auto.
     eapply OUTOFREACH; eauto.
     apply Fwd12. apply H0.
    rewrite PERMS1 in H1.
      assumption.
  specialize (PERMS1 _ _ k p H H0).
    apply PERMS1.
      apply PERMS2. destruct H as [? ?]. split; auto.
      intros bb; intros. intros N.
      unfold loc_out_of_reach in H.
      case_eq (f1 bb); intros.
        destruct p0. rewrite (INCR _ _ _ H4) in H3.
        inv H3.
        apply (H _ _ H4). apply MAXPERMS; trivial.
           eapply (Mem.valid_block_inject_1 _ _ _ _ _ _ H4 INJ1).
      destruct (SEP _ _ _ H4 H3).
        contradiction.
    apply Fwd12. apply H0.
    apply H1.
  (* loads *)
  rewrite <- LOADS1; try assumption.
  apply LOADS2; try assumption.
     destruct H.
     split; trivial.
     eapply OUTOFREACH; eassumption.
  apply PERMS1; trivial.
    apply Mem.perm_valid_block in H0. assumption.
Qed.

End RelyGuaranteeSemanticsLemmas.

Definition blockmap := block -> bool.

Section RelyGuaranteeSemanticsFunctor.
Context {G C: Type}.
Variable csem: CoopCoreSem G C.

Definition rg_step (ge: G) (x: blockmap*C) (m: mem) (x': blockmap*C) (m': mem) :=
  match x, x' with (f, c), (f', c') => 
    corestep csem ge c m c' m' /\
    (forall b, f' b=true -> f b=true \/ (Mem.nextblock m <= b < Mem.nextblock m')%positive)
  end.


Program Definition RelyGuaranteeCoreSem: CoreSemantics G (blockmap*C) mem :=
  Build_CoreSemantics G (blockmap*C) mem 
    (*initial mem deprecated here
    (initial_mem csem)*)
    (*make_initial_core*)
    (fun ge v vs => match initial_core csem ge v vs with
                    | Some c => Some (fun _ => false, c)
                    | None => None
                    end)
    (*at_external*)
    (fun x => at_external csem (snd x))
    (*after_external*)
    (fun retv x => match after_external csem retv (snd x) with
                   | Some c => Some (fst x, c)
                   | None => None
                   end)
    (*halted*)
    (fun x => halted csem (snd x))
    (*corestep*)
    rg_step
    _ _ _ _.
Next Obligation.
destruct H as [H1 H2]; apply corestep_not_at_external in H1; auto.
Qed.
Next Obligation.
destruct H as [H1 H2]; apply corestep_not_halted in H1; auto.
Qed.
Next Obligation. apply (at_external_halted_excl csem c). Qed.
Next Obligation. 
simpl in H.
case_eq (after_external csem retv c0); intros. 
rewrite H0 in H; inv H.
apply after_at_external_excl in H0; auto.
rewrite H0 in H; congruence.
Qed.

Lemma rg_csem:
  forall ge c f m c' f' m',
  corestep RelyGuaranteeCoreSem ge (f, c) m (f', c') m' -> 
  corestep csem ge c m c' m'.
Proof.
intros until m'; intros H1.
inv H1.
auto.
Qed.

Program Definition RelyGuaranteeCoopSem: CoopCoreSem G (blockmap*C) :=
  Build_CoopCoreSem G (blockmap*C)
    RelyGuaranteeCoreSem (*_ _*) _.
Next Obligation.
inv CS.
apply corestep_fwd in H; auto.
Qed.
(*Obligion for initial_mem - deprecated
Next Obligation.
apply initmem_wd in H.
auto.
Qed.*)

Program Definition RGSemantics: RelyGuaranteeSemantics G (blockmap*C) :=
  Build_RelyGuaranteeSemantics G (blockmap*C)
   RelyGuaranteeCoopSem
   (fun x b => fst x b = true) _ _ _ _.
Next Obligation.
simpl.
destruct (b0 b).
left; auto.
right; auto.
Qed.
Next Obligation. 
simpl.
destruct (initial_core csem ge v vs).
inv H; auto.
congruence.
Qed.
Next Obligation. 
destruct H; auto. Qed.
Next Obligation. 
simpl in *|-*; destruct (after_external csem retv c); try solve[congruence].
Qed.

End RelyGuaranteeSemanticsFunctor.