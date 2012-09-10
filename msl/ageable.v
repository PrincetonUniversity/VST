(*
 * Copyright (c) 2009-2010, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import msl.base.

Open Local Scope nat_scope.

Record ageable_facts (A:Type) (level: A -> nat) (age1:A -> option A)  :=
{ af_unage : forall x':A, exists x, age1 x = Some x'
; af_level1 : forall x, age1 x = None <-> level x = 0
; af_level2 : forall x y, age1 x = Some y -> level x = S (level y)
}.

Implicit Arguments af_unage [[A] [level] [age1]].
Implicit Arguments af_level1 [[A] [level] [age1]].
Implicit Arguments af_level2 [[A] [level] [age1]].

Class ageable (A:Type) := mkAgeable
{ level : A -> nat
; age1 : A -> option A
; age_facts : ageable_facts A level age1
}.

Definition age {A} `{ageable A} (x y:A) := age1 x = Some y.

Lemma af_wf {A} `{ageable A} : 
 well_founded (fun x y => age y x).
Proof.
  intros.
  intro.
  remember (level a).
  revert a Heqn.
  induction n; intros; constructor; intros.
  apply (af_level2 age_facts) in H0.
  rewrite H0 in Heqn.
  inversion Heqn.
  copy H0.
  apply (af_level2 age_facts) in H0.
  apply IHn.
  omega.
Qed.
Implicit Arguments af_wf.

Definition age_induction {A} `{ageable A} :=
  well_founded_induction (af_wf _).

Definition fashionR {A1} `{ageable A1} {A2}`{ageable A2} (x:A1) (y: A2) : Prop :=
  level x = level y.

Lemma fashionR_refl {A} `{ageable A} : reflexive _ fashionR.
Proof.
  repeat intro; hnf; auto.
Qed.

Lemma fashionR_trans {A} `{ageable A} {B} `{ageable B} {C} `{ageable C} : 
    forall (x: A) (y: B) (z: C), fashionR x y -> fashionR y z -> fashionR x z.
Proof.
  unfold fashionR; intros; congruence.
Qed.

Lemma fashionR_sym {A} `{ageable A} {B} `{ageable B}: 
   forall (x: A) (y: B), fashionR x y -> fashionR y x.
Proof.
  unfold fashionR; intros; auto.
Qed.

Lemma age_level {A} `{ageable A} : forall (x y:A),
  age x y -> level x = S (level y).
Proof.
  intros.
  apply (af_level2 age_facts); auto.
Qed.

Lemma age1_level0 {A} `{ageable A} : forall (x:A),
  age1 x = None <-> level x = 0.
Proof.
  intros; apply (af_level1 age_facts).
Qed.

Section level'.
  Variable A:Type.
  Variable ag:ageable A.

  Require Recdef.
  Function level' (x:A) { wf (transp _ (@age A ag)) x } : nat :=
    match age1 x with
    | None => 0
    | Some x' => S (level' x')
    end.
    hnf; auto.
    unfold transp; apply (af_wf _).
  Defined.
  
  Theorem level_level' : forall x:A, level x = level' x.
  Proof.
    intro x; induction x using age_induction; intros.
    rewrite level'_equation.
    case_eq (age1 x); intros.
    rewrite (af_level2 age_facts x a); auto.
    rewrite <- age1_level0; auto.
  Qed.
End level'.

Lemma levelS_age1 {A} `{ageable A} : forall (x:A) n,
  level x = S n ->
  exists y, age1 x = Some y.
Proof.
  intros; rewrite level_level' in H0.
  rewrite level'_equation in H0.
  destruct (age1 x); eauto.
  inv H0.
Qed.

Lemma age1_levelS {A} `{ageable A} : forall (x y:A),
  age1 x = Some y ->
  exists n, level x = S n.
Proof.
  intros; rewrite level_level'.
  rewrite level'_equation.
  destruct (age1 x); eauto.
  inv H0.
Qed.

Lemma age1_level0_absurd {A} `{ageable A} : forall (x y:A),
  age1 x = Some y ->
  level x = 0 ->
  False.
Proof.
  intros.
  rewrite <- age1_level0 in H1.
  rewrite H0 in H1; discriminate.
Qed.

Lemma age1None_levelS_absurd {A} `{ageable A} : forall (x:A) n,
  age1 x = None ->
  level x = S n ->
  False.
Proof.
  intros.
  rewrite age1_level0 in H0.
  rewrite H0 in H1; discriminate.
Qed.

Section RtRft.
  Variable A:Type.
  Variable R:relation A.

  Let Rt := clos_trans A R.
  Let Rft := clos_refl_trans A R.

  Lemma Rt_Rft : forall x y, Rt x y -> Rft x y.
  Proof.
    intros; elim H; intros.
    apply rt_step; auto.
    eapply rt_trans; eauto.
  Qed.

  Lemma Rt_Rft_trans : forall x y z, Rt x y -> Rft y z -> Rt x z.
  Proof.
    intros x y z H H1; revert x H; elim H1; intros; auto.
    eapply t_trans; eauto; apply t_step; auto.
  Qed.

  Lemma Rft_Rt_trans : forall x y z, Rft x y -> Rt y z -> Rt x z.
  Proof.
    intros x y z H; revert z; elim H; intros; auto.
    eapply t_trans; eauto; apply t_step; auto.
  Qed.

  Lemma transpose_clos_trans : forall A R x y,
    clos_trans A (transp A R) x y <-> transp A (clos_trans A R) x y.
  Proof.
    unfold transp; intuition.
    
    elim H; intros.
    apply t_step; auto.
    apply t_trans with y0; auto.

    elim H; intros.
    apply t_step; auto.
    apply t_trans with y0; auto.
  Qed.
End RtRft.

Hint Resolve rt_refl.

Definition laterR {A} `{ageable A} : relation A := clos_trans A age.
Definition necR   {A} `{ageable A} : relation A := clos_refl_trans A age.

Require Wellfounded.
Lemma laterR_wf {A} `{ageable A} :
  well_founded (transp _ laterR).
Proof.
  intros.
  hnf; intro.
  induction a using
    (well_founded_induction (Wellfounded.Transitive_Closure.wf_clos_trans _ (fun x y => age y x) (af_wf _))).
  constructor; intros.
  unfold laterR in H1.
  rewrite <- transpose_clos_trans in H1.
  apply H0; auto.
Qed.

Definition laterR_induction {A} `{ageable A} :=
  @well_founded_induction A (transp A laterR) laterR_wf.

Lemma age_irreflexive {A}  `{ageable A}: forall x, age x x -> False.
Proof.
  intros x.
  induction x using age_induction; intros.
  apply H0 with x; auto.
Qed.

Lemma laterR_irreflexive {A} `{HA: ageable A} : forall x, laterR x x -> False.
Proof.
  intros x.
  induction x using laterR_induction; intros.
  apply H with x; auto.
Qed.

Lemma nec_refl_or_later {A} `{ageable A} : forall x y,
  necR x y -> x = y \/ laterR x y.
Proof.
  intros.
  elim H0; intros; auto.
  right; apply t_step; auto.
  destruct H2; destruct H4; subst; auto.
  right; apply t_trans with y0; auto.
Qed.

Lemma necR_antisym {A} `{ageable A} : forall x y,
  necR x y -> necR y x -> x = y.
Proof.
  intros.
  apply nec_refl_or_later in H0.
  apply nec_refl_or_later in H1.
  intuition.
  elim (laterR_irreflexive x).
  eapply t_trans; eauto.
Qed.

Lemma age_later_nec {A} `{HA: ageable A} : forall x y z,
  age x y ->
  laterR x z ->
  necR y z.
Proof.
  intros x y z H H1; revert y H.
  induction H1; intros.
  replace y0 with y.
  apply rt_refl.
  unfold age in *; congruence.
  apply rt_trans with y; auto.
  apply IHclos_trans1; auto.
  apply Rt_Rft; auto.
Qed.

Lemma necR_level {A} `{X: ageable A} : forall (x y:A),
  necR x y ->
  level x >= level y.
Proof.
  intros x y H; induction H; auto.
  rewrite (age_level x y); auto.
  omega.
Qed.

Lemma laterR_level {A} `{X: ageable A} : forall (x y:A),
  laterR x y ->
  level x > level y.
Proof.
  intros x y H; induction H; auto.
  rewrite (age_level x y); auto.
  omega.
Qed.

Section NAT_AGEABLE.
  
  Definition natLevel (x:nat) : nat := x.
  Definition natAge1 (x:nat) : option nat :=
    match x with
    | 0 => None
    | S n => Some n
    end.
  Definition natUnage (x:nat) : nat := S x.

  Lemma ag_nat_facts : 
    ageable_facts nat natLevel natAge1.
  Proof.
    constructor.
    intros; exists (S x'); compute; auto.
    intro x; destruct x; intuition; inv H.
    firstorder;
      destruct x; inv H; compute; eauto.
  Qed.

  Definition ag_nat : ageable nat :=
    mkAgeable nat natLevel natAge1 ag_nat_facts.

  Lemma nec_nat : forall (n n':nat),
    @necR _ ag_nat n n' <-> n' <= n.
  Proof.
    intros. split; intro.
    induction H.
    destruct x; inv H; auto.
    auto.
    omega.
    
    induction H.
    apply rt_refl.
    apply rt_trans with m.
    apply rt_step. compute; auto.
    auto.
  Qed.

  Lemma later_nat : forall (n n':nat),
    @laterR _ ag_nat n n' <-> n' < n.
  Proof.
    intros. split; intro.
    induction H.
    destruct x; simpl in H.
    inv H.
    inv H. omega.
    omega.
    hnf in H.
    inv H.
    apply t_step.
    compute; auto.
    apply Rt_Rft_trans with m.
    apply t_step. compute; auto.
    change (@necR _ ag_nat m n').
    rewrite nec_nat.
    omega.
  Qed.

End NAT_AGEABLE.


Lemma laterR_level' {A} `{H : ageable A}: forall {w1 w2: A}, laterR w1 w2 -> @laterR _ ag_nat (level w1) (level w2).
Proof.
induction 1.
constructor 1. apply age_level in H0. rewrite H0; reflexivity.
constructor 2 with (level y); auto.
Qed.

Lemma necR_nat {A} `{H : ageable A}:
    forall {x y: A}, necR x y -> @necR nat ag_nat (level x) (level y).
  Proof.
    intros. apply necR_level in H0.
     induction H0; simpl in *. constructor 2.
     constructor 3 with m. constructor 1. constructor.
     auto.
  Qed.

Section BIJECTION.
  Variable A B : Type.
  Variable ag: ageable A.
  Variable bijAB: bijection A B.

  Let levelB (x:B) : nat :=
    level (bij_g _ _ bijAB x).

  Let age1B  (x: B) : option B :=
     match age1 (bij_g _ _ bijAB x) with
     | Some y => Some (bij_f _ _ bijAB y)
     | None => None
     end.

  Let ageB (x y: B) :=age1B x = Some y.

  Lemma age_bij_unage : 
    forall x', exists x, age1B x = Some x'.
  Proof.
    unfold age1B, levelB; simpl; intros.
    destruct bijAB as [f g fg gf]; simpl in *.
    destruct (af_unage age_facts (g x')) as [y ?].
   exists (f y). rewrite gf. rewrite H. f_equal. apply fg. 
  Qed.

  Lemma age_bij_level1 :
    forall x, age1B x = None <-> levelB x = 0.
  Proof.
    intros.
    unfold age1B, levelB; simpl.
    destruct bijAB as [f g fg gf]; simpl.
    case_eq (age1 (g x)); intuition; try discriminate.
    rewrite <- age1_level0 in H1.
    rewrite H0 in H1; discriminate.
    rewrite <- age1_level0; auto.
  Qed.

  Lemma age_bij_level2 :
    forall x y, age1B x = Some y -> levelB x = S (levelB y).
  Proof.
    intros.
    unfold age1B, levelB in *; simpl in *.
    destruct bijAB as [f g fg gf]; simpl in *.
    case_eq (age1 (g x)); intros; rewrite H0 in H; inv H.
    rewrite gf.
    apply (af_level2 age_facts); auto.
  Qed.

  Lemma ag_bij_facts : ageable_facts B levelB age1B.
  Proof.
    constructor.
    exact age_bij_unage.
    exact age_bij_level1.
    exact age_bij_level2.
  Qed.

  Definition ag_bij : ageable B :=
    mkAgeable B levelB age1B ag_bij_facts.
End BIJECTION.

Section PROD.
  Variable A B : Type.
  Variable agA: ageable A.
  
  Let levelAB (x:prod A B) := level (fst x).
  Let age1AB (x:prod A B) :=
    match age1 (fst x) with
    | None => None
    | Some a' => Some (a',snd x)
    end.

  Lemma ag_prod_facts : ageable_facts (prod A B) levelAB age1AB.
  Proof.
    constructor.
    unfold levelAB, age1AB; simpl; intros.
    destruct (af_unage age_facts (fst x')) as [y1 ?].
    exists (y1, snd x'). simpl. rewrite H. f_equal. destruct x'; auto.
    intros [a b]; firstorder.
    unfold age1AB in H; simpl in H.
    case_eq (age1 a); intros; rewrite H0 in H; inv H.
    unfold levelAB; simpl.
    rewrite <- age1_level0; auto.
    unfold levelAB in H.
    simpl in H.
    rewrite <- age1_level0 in H.
    unfold age1AB; simpl.
    rewrite H; auto.
    intros.
    unfold age1AB in H.
    unfold levelAB.
    destruct x; simpl in *.
    case_eq (age1 a); intros; rewrite H0 in H; inv H.
    simpl.
    apply age_level; auto.
  Qed.

  Definition ag_prod :=
    mkAgeable (prod A B) levelAB age1AB ag_prod_facts.

  Lemma prod_nec_split : forall n x n' x',
    @necR (prod A B) ag_prod (n,x) (n',x') <-> necR n n' /\ x = x'.
  Proof.
    intros; split; intro.
    remember (n,x) as w.
    remember (n',x') as w'.
    revert n x n' x' Heqw Heqw'.
    induction H; simpl; intros; subst; auto.
    unfold age in H. simpl in H.
    unfold age1AB in H. simpl in H.
    case_eq (age1 n); intros; rewrite H0 in H; inv H.
    split; auto.
    apply rt_step. auto.
    inv Heqw'.
    split; auto.
    apply rt_refl.
    spec IHclos_refl_trans1 n x0 (fst y) (snd y).
    spec IHclos_refl_trans1; auto.
    spec IHclos_refl_trans1; destruct y; auto.
    simpl in *.
    spec IHclos_refl_trans2 a b n' x'.
    spec IHclos_refl_trans2; auto.
    spec IHclos_refl_trans2; auto.
    intuition. eapply rt_trans; eauto.
    congruence.

    destruct H; subst.
    induction H.
    apply rt_step. hnf.
    hnf in H. simpl.
    unfold age1AB. simpl. rewrite H. auto.
    apply rt_refl.
    eapply rt_trans; eauto.
  Qed.

  Lemma prod_later_split : forall n x n' x',
    @laterR (prod A B) ag_prod (n,x) (n',x') <-> laterR n n' /\ x = x'.
  Proof.
    intros; split; intro.
    remember (n,x) as w.
    remember (n',x') as w'.
    revert n x n' x' Heqw Heqw'.
    induction H; simpl; intros; subst; auto.
    unfold age in H. simpl in H.
    unfold age1AB in H; simpl in H.
    case_eq (age1 n); intros; rewrite H0 in H; inv H.
    split; auto.
    apply t_step. compute. auto.
    spec IHclos_trans1 n x0 (fst y) (snd y).
    spec IHclos_trans1; auto.
    spec IHclos_trans1; destruct y; auto.
    simpl in *.
    spec IHclos_trans2 a b n' x'.
    spec IHclos_trans2; auto.
    spec IHclos_trans2; auto.
    intuition. eapply t_trans; eauto.
    congruence.

    destruct H; subst.
    induction H.
    apply t_step. 
    hnf; simpl. unfold age1AB. simpl; rewrite H. auto.
    eapply t_trans; eauto.
  Qed.

End PROD.

Section PROD'.
  Variable A B : Type.
  Variable agB: ageable B.
  
  Let levelAB (x:prod A B) := level (snd x).
  Let age1AB (x:prod A B) :=
    match age1 (snd x) with
    | None => None
    | Some a' => Some (fst x, a')
    end.

  Lemma ag_prod'_facts : ageable_facts (prod A B) levelAB age1AB.
  Proof.
    constructor.
    unfold levelAB, age1AB; simpl; intros.
    destruct (af_unage age_facts (snd x')) as [y2 ?].
    exists (fst x', y2). simpl. rewrite H. f_equal. destruct x'; auto.
    intros [a b]; firstorder.
    unfold age1AB in H; simpl in H.
    case_eq (age1 b); intros; rewrite H0 in H; inv H.
    unfold levelAB; simpl.
    rewrite <- age1_level0; auto.
    unfold levelAB in H.
    simpl in H.
    rewrite <- age1_level0 in H.
    unfold age1AB; simpl.
    rewrite H; auto.
    intros.
    unfold age1AB in H.
    unfold levelAB.
    destruct x; simpl in *.
    case_eq (age1 b); intros; rewrite H0 in H; inv H.
    simpl.
    apply age_level; auto.
  Qed.

  Definition ag_prod' :=
    mkAgeable (prod A B) levelAB age1AB ag_prod'_facts.

  Lemma prod'_nec_split : forall n x n' x',
    @necR (prod A B) ag_prod' (x,n) (x',n') <-> necR n n' /\ x = x'.
  Proof.
    intros; split; intro.
    remember (x,n) as w.
    remember (x',n') as w'.
    revert n x n' x' Heqw Heqw'.
    induction H; simpl; intros; subst; auto.
    unfold age in H. simpl in H.
    unfold age1AB in H. simpl in H.
    case_eq (age1 n); intros; rewrite H0 in H; inv H.
    split; auto.
    apply rt_step. auto.
    inv Heqw'.
    split; auto.
    apply rt_refl.
    spec IHclos_refl_trans1 n x0 (snd y) (fst y).
    spec IHclos_refl_trans1; auto.
    spec IHclos_refl_trans1; destruct y; auto.
    simpl in *.
    spec IHclos_refl_trans2 b a n' x'.
    spec IHclos_refl_trans2; auto.
    spec IHclos_refl_trans2; auto.
    intuition. eapply rt_trans; eauto.
    congruence.

    destruct H; subst.
    induction H.
    apply rt_step. hnf.
    hnf in H. simpl.
    unfold age1AB. simpl. rewrite H. auto.
    apply rt_refl.
    eapply rt_trans; eauto.
  Qed.

  Lemma prod'_later_split : forall n x n' x',
    @laterR (prod A B) ag_prod' (x,n) (x',n') <-> laterR n n' /\ x = x'.
  Proof.
    intros; split; intro.
    remember (x,n) as w.
    remember (x',n') as w'.
    revert n x n' x' Heqw Heqw'.
    induction H; simpl; intros; subst; auto.
    unfold age in H. simpl in H.
    unfold age1AB in H; simpl in H.
    case_eq (age1 n); intros; rewrite H0 in H; inv H.
    split; auto.
    apply t_step. compute. auto.
    spec IHclos_trans1 n x0 (snd y) (fst y).
    spec IHclos_trans1; auto.
    spec IHclos_trans1; destruct y; auto.
    simpl in *.
    spec IHclos_trans2 b a n' x'.
    spec IHclos_trans2; auto.
    spec IHclos_trans2; auto.
    intuition. eapply t_trans; eauto.
    congruence.

    destruct H; subst.
    induction H.
    apply t_step. 
    hnf; simpl. unfold age1AB. simpl; rewrite H. auto.
    eapply t_trans; eauto.
  Qed.

End PROD'.

Fixpoint composeOptN (A: Type) (f: A -> option A)
         (n: nat) (w: A) {struct n} : option A :=
 match n  with 
 | S n' => match f w with Some w' => composeOptN A f n' w' | None => None end
 | O => Some w
 end.
Implicit Arguments composeOptN.

Definition ageN {A} `{ageable A}: nat -> A -> option A := composeOptN age1.

Lemma ageN1  {A} `{ageable A}: ageN 1 = age1.
Proof.
intros.
unfold ageN. simpl.
extensionality phi.
case_eq (age1 phi); intros; try rewrite H; auto.
Qed.

Lemma ageN_compose {A} `{agA : ageable A}: 
 forall a b c phi1 phi2 phi3,ageN a phi1 = Some phi2 ->
       ageN b phi2 = Some phi3 ->  (a+b=c)%nat ->  ageN c phi1 = Some phi3.
Proof.
unfold ageN in *.
induction a; simpl; intros.
subst. inversion H; clear H. auto.
subst c.
case_eq (age1 phi1); intros; rewrite H1 in H; try discriminate.
simpl.
rewrite H1.
eapply IHa; eauto.
Qed.

Lemma ageN_compose' {A} `{agA : ageable A}:
  forall a b phi1 phi3,
   ageN (a+b)%nat phi1 = Some phi3 -> exists phi2, ageN a phi1 = Some phi2 /\ ageN b phi2 = Some phi3.
Proof.
intros.
case_eq (ageN a phi1); intros.
rename a0 into phi.
exists phi.
split; auto.
case_eq (ageN b phi); intros.
rename a0 into phi0.
generalize (ageN_compose a b (a+b) phi1 _ _ H0 H1 (refl_equal _)); intro.
rewrite H in H2; auto.
elimtype False.
revert phi1 phi H H1 H0; induction a; intros.
simpl in *.
inv H0.
rewrite H in H1; discriminate.
replace (S a + b)%nat with (S (a+b))%nat in H by omega.
unfold ageN in *;
simpl in *.
case_eq (age1 phi1); intros; rewrite H2 in H; try discriminate.
rewrite H2 in H0.
eapply IHa; eauto.
elimtype False.
unfold ageN in *.
revert phi1 H H0; induction a; intros.
simpl in *. discriminate.
replace (S a + b)%nat with (S (a+b))%nat in H by omega.
simpl in *.
revert H H0; case_eq (age1 phi1); intros; try discriminate.
eapply IHa; eauto.
Qed.

Lemma necR_evolve {A} `{agA : ageable A}:
    necR = fun (phi phi': A) => exists n, ageN n phi = Some phi'.
Proof.
extensionality w w'.
apply prop_ext; split; intros.
unfold necR in H.
induction H.
exists 1%nat. rewrite ageN1.
simpl.
auto.
exists O; auto.
destruct IHclos_refl_trans1 as [n1 ?].
destruct IHclos_refl_trans2 as [n2 ?].
exists (n1+n2)%nat.
eapply ageN_compose; eauto.
destruct H as [n ?].
revert w w' H; induction n; intros.
inv H.
constructor 2.
unfold ageN in H.
simpl in H.
revert H; case_eq (age1 w); intros; try discriminate.
constructor 3 with a.
constructor 1; auto.
apply IHn; auto.
Qed.

Lemma age_noetherian  {A} `{ageable A}: forall phi, exists n, ageN n phi = None.
Proof.
  intros.
  induction phi using age_induction.
  rename x into phi.
  case_eq (age1 phi); intros.
  generalize H1; intros.
  apply H0 in H1.
  destruct H1 as [n ?].
  exists (S n).
  unfold ageN; simpl.
  rewrite H2; auto.
  exists (S O); simpl.
  unfold ageN; simpl.
  rewrite H1.
  auto.
Qed.

Lemma predicate_max:
  forall (F: nat -> Prop) (Fdec: forall n, {F n}+{~ F n}) n,
  F 0%nat ->
  ~ F n ->
  exists i, F i /\ (i<n)%nat /\ ~ F (S i).
Proof.
intros.
assert (forall m, (m <= n)%nat ->
         (forall k, (k<m)%nat -> F k) \/ 
         (exists i, F i /\ (i<m)%nat /\ ~ F (S i))).
induction m.
left; intros.
elimtype False; omega.
intro.
assert (m<=n)%nat; try omega.
destruct (IHm H2).
assert (m < n \/ m = n)%nat; try omega.
destruct H4.
destruct (Fdec m) as [?H|?H].
left.
intros.
assert (k < m \/ k = m)%nat; try omega.
destruct H7.
auto.
subst k; auto.
right.
exists (Peano.pred m).
destruct m.
contradiction.
replace (Peano.pred (S m)) with m; try omega.
split.
apply H3; try omega.
split; try omega.
auto.
subst m.
right.
destruct n.
contradiction.
exists n; repeat split; auto; try omega.
right.
destruct H3 as [i H4].
destruct H4.
destruct H4.
exists i; repeat split; auto; omega.
assert (n <= n)%nat; try omega.
destruct (H1 _ H2).
destruct n; try contradiction.
exists n; repeat split; auto; try omega.
auto.
Qed.

Lemma age_noetherian'  {A} `{agA : ageable A}: 
       forall phi, exists! n, exists phi', ageN n phi = Some phi' /\ age1 phi' = None.
Proof.
intros.
destruct (age_noetherian phi) as [n ?].
assert (Fdec: forall n, {ageN n phi <> None}+{~( ageN n phi <> None)}) 
  by (intros; destruct (ageN n0 phi); auto; left; intro Hx; inversion Hx).
destruct (predicate_max (fun n => ageN n phi <> None) Fdec n) as [i [? [? ?]]].
intro. inv H0.
intro.
rewrite H in H0.
contradiction H0; auto.
exists i.
split.
revert H0; case_eq (ageN i phi); intros.
exists a; split; auto.
revert H2; case_eq (ageN (S i) phi); intros.
contradiction H4.
intro Hx; inv Hx.
clear - H0 H2.
revert phi a H0 H2; induction i; intros.
inv H0.
rewrite ageN1 in H2; auto.
unfold ageN in *.
simpl in H0.
revert H0; case_eq (age1 phi); intros; try discriminate.
simpl in H2.
rewrite H in H2.
eapply IHi.
eauto.
simpl.
auto.
contradiction H3; auto.
intros.
destruct H3 as [phi' [? ?]].
assert (ageN (S i) phi = None).
clear - H2.
revert H2; case_eq (ageN (S i) phi); intros.
contradict H2. intro Hx; inv Hx.
auto. clear H2.
clear - H0 H5 H3 H4.
revert H0; case_eq (ageN i phi); intros.
2: contradiction H0; auto.
clear H0.
assert (age1 a = None).
clear - H H5.
revert phi H5 H; induction i; intros.
inv H; rewrite ageN1 in H5; auto.
unfold ageN in *.
revert H H5; simpl. case_eq (age1 phi); intros; try discriminate.
eapply IHi; eauto.
clear H5.
assert (forall i d phi a a', ageN i phi = Some a -> ageN (i+d) phi = Some a' -> age1 a' = None -> age1 a = None -> d=0%nat).
clear.
induction i; intros.
inv H.
destruct d; auto.
simpl in H0.
unfold ageN in H0. simpl in H0.
rewrite H2 in H0. inv H0.
unfold ageN in H, H0. simpl in *.
revert H; case_eq (age1 phi); intros; try discriminate.
rewrite H in H0.
eauto.
assert (i<x' \/ i=x' \/ i>x')%nat by omega.
destruct H2 as [?| [?| ?]]; auto.
replace x' with (i+(x'-i))%nat in H3 by omega.
specialize (H1 _ _ _ _ _ H H3 H4 H0).
omega.
replace i with (x'+(i-x'))%nat in H by omega.
specialize (H1 _ _ _ _ _ H3 H H0 H4).
omega.
Qed.

Lemma ageable_ext:
   forall A (B C: ageable A),
      @age1 _ B = @age1 _ C -> @level _ B = @level _ C -> B=C.
Proof.
intros.
destruct B; destruct C.
simpl in *.
subst age3. subst level0.
replace age_facts1 with age_facts0; auto.
apply proof_irr.
Qed.

Lemma necR_linear {A} `{H : ageable A}:
  forall {a b c}, necR a b -> necR a c -> necR b c \/ necR c b.
Proof.
intros.
apply trans_rt1n in H0.
apply trans_rt1n in H1.
revert c H1; induction H0; intros; auto.
left; apply rt1n_trans; auto.
inversion H2; subst.
right.
apply rt_trans with y.
constructor 1; auto.
apply rt1n_trans; auto.
unfold age in H0,H3.
rewrite H0 in H3; inv H3.
destruct (IHclos_refl_trans_1n _ H4); auto.
Qed.

Lemma necR_linear' {A} `{H : ageable A}:
   forall {a b c}, necR a b -> necR a c -> level b = level c -> b=c.
Proof.
intros.
destruct (necR_linear H0 H1).
clear - H2 H3.
apply nec_refl_or_later in H3.
destruct H3; auto.
apply laterR_level in H0; unfold fashionR in H2; elimtype False; omega.
apply nec_refl_or_later in H3.
destruct H3; auto.
apply laterR_level in H3; unfold fashionR in H2; elimtype False; omega.
Qed.

Lemma laterR_necR {A} `{agA : ageable A}: 
  forall {x y}, laterR x y -> necR x y.
Proof.
induction 1; intros.
constructor; auto.
econstructor 3; auto.
apply rt_trans with y; auto.
Qed.

Lemma necR_refl {A} `{H : ageable A}:
  forall phi, necR phi phi.
Proof.
intros; constructor 2.
Qed.

Hint Resolve @necR_refl.

Lemma necR_trans  {A} `{H : ageable A}:
  forall phi1 phi2 phi3, necR phi1 phi2 -> necR phi2 phi3 -> necR phi1 phi3.
Proof.
intros.
econstructor 3; eauto.
Qed.

Lemma necR_laterR {A} `{agA : ageable A}:
  forall w1 w2 w3, necR w1 w2 -> laterR w2 w3 -> laterR w1 w3.
Proof.
intros.
revert w3 H0; induction H; intros.
econstructor 2. constructor 1; eauto. apply H0.
auto.
auto.
Qed.
