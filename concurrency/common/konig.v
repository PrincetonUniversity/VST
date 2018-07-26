Require Import Coq.Logic.ChoiceFacts.
Require Import Coq.omega.Omega.

Tactic Notation "assert_specialize" hyp(H) :=
  match type of H with
    forall x : ?P, _ =>
    let Htemp := fresh "Htemp" in
    assert P as Htemp; [ | specialize (H Htemp); try clear Htemp ]
  end.

(** * Ramsey theorem (with the necessary set-theoretic definitions) *)

Definition intersection {X} (A B : X -> Prop) := fun x => A x /\ B x.
Definition minus {X} (A B : X -> Prop) := fun x => A x /\ ~B x.
Definition subset {X} (A B : X -> Prop) := forall x, A x -> B x.
Definition finite {X} (A : X -> Prop) := exists n f, forall x, A x -> exists i, i < n /\ f i = x.
Definition infinite (A : nat -> Prop) := forall b, exists a, b <= a /\ A a.
Definition image {X Y} (f : X -> Y) (A : X -> Prop) : Y -> Prop := fun y => exists x, A x /\ y = f x.
Definition preimage {X Y} (f : X -> Y) (B : Y -> Prop) : X -> Prop := fun x => B (f x).

Lemma infinite_subset (A B : nat -> Prop) :
  subset A B -> infinite A -> infinite B.
Proof.
  intros s i n; destruct (i n) as (a, H).
  exists a; intuition.
Qed.

Lemma infinite_minus A B :
  (forall P, ~~P -> P) ->
  infinite A ->
  ~ infinite (intersection A B) ->
  infinite (minus A B).
Proof.
  intros DN ia nib x.
  destruct (ia x) as (a & La & Ha).
  apply DN; intros Nex; apply nib; clear nib.
  intros y.
  destruct (ia (x + y)) as (a' & La' & Ha').
  exists a'; split.
  - omega.
  - split. auto.
    apply DN; intros nB.
    apply Nex.
    exists a'; split.
    + omega.
    + split; auto.
Qed.

Lemma image_subset {X Y} A B (f : X -> Y) :
  subset A B ->
  subset (image f A) (image f B).
Proof.
  intros s y (x & Ax & ->); exists x; auto.
Qed.

Lemma ramsey_preimage {X} (N : nat -> Prop) (f : nat -> X) :
  (forall P, P \/ ~P) ->
  finite (image f N) ->
  infinite N ->
  exists x, infinite (intersection N (preimage f (eq x))).
Proof.
  intros EM (n & enumfN & bound).
  revert N bound.
  induction n; intros N bound inf.
  - exfalso.
    destruct (inf 0) as (n & _ & Nn).
    specialize (bound (f n) ltac:(compute; eauto)).
    destruct bound as (i & Hi & _).
    inversion Hi.
  - destruct (EM (infinite (intersection N (preimage f (eq (enumfN n)))))) as [Ye|No].
    + exists (enumfN n); auto.
    + pose (N' := minus N (preimage f (eq (enumfN n)))).
      specialize (IHn N').
      assert_specialize IHn.
      {
        (* proof that the image is of card <= n (instead of n+1) *)
        intros x N'x.
        specialize (bound x).
        assert_specialize bound.
        {
          revert N'x.
          apply image_subset.
          compute. tauto.
        }
        destruct bound as (i & Li & E).
        exists i; split; auto.
        rewrite <-E in N'x.
        cut (i <> n); [ omega | ]. intros ->.
        unfold image in N'x.
        destruct N'x as (x' & N'x'& Efx').
        compute in *; tauto.
      }
      assert_specialize IHn.
      {
        (* proof that N' = N \ f-1({}) is still infinite *)
        unfold N'. clear N' IHn. rename N into A.
        revert No; generalize (preimage f (eq (enumfN n))) as B; intros B No.
        apply infinite_minus; auto.
        intros P; destruct (EM P); tauto.
      }
      destruct IHn as (x, IHn). exists x.
      eapply infinite_subset; [ | apply IHn ]. clear IHn.
      compute.
      tauto.
Qed.

Lemma EM_ABS : (forall P, P \/ ~P) <-> (forall P, ~~P -> P).
Proof.
  split.
  - intros em P np. destruct (em P); tauto.
  - intros abs P. apply abs; tauto.
Qed.

Fixpoint zip {X} (f1 f2 : nat -> X) n :=
  match n with
  | O => f1 O
  | S O => f2 0
  | S (S n) => zip (fun n => f1 (S n)) (fun n => f2 (S n)) n
  end.

Lemma zip_ext {X} f1 f2 g1 g2 :
  (forall x, f1 x = g1 x) ->
  (forall x, f2 x = g2 x) ->
  forall k, @zip X f1 f2 k = @zip X g1 g2 k.
Proof.
  intros E1 E2 k.
  cut (zip f1 f2 k = zip g1 g2 k /\
       zip f1 f2 (S k) = zip g1 g2 (S k)); [intuition|].
  revert f1 f2 g1 g2 E1 E2.
  induction k. simpl; auto.
  intros f1 f2 g1 g2 E1 E2.
  split. now apply IHk; auto.
  simpl. apply IHk; eauto.
Qed.

Lemma zip_1 {X} f1 f2 n : @zip X f1 f2 (2 * n) = f1 n.
Proof.
  replace (f1 n) with (f1 (0 + n)) by (f_equal; omega).
  transitivity (zip (fun n => f1 (0 + n)) (fun n => f2 (0 + n)) (2 * n)).
  - apply zip_ext; intros; auto.
  - generalize 0 at 1 2 4 as k; induction n; auto; intros k.
    replace (2 * S n) with (S (S (2 * n))) by omega.
    unfold zip; fold (@zip X).
    replace (k + S n) with (S k + n) by omega.
    rewrite <-IHn.
    apply zip_ext; intros; f_equal; omega.
Qed.

Lemma zip_2 {X} f1 f2 n : @zip X f1 f2 (1 + 2 * n) = f2 n.
Proof.
  replace (f2 n) with (f2 (0 + n)) by (f_equal; omega).
  transitivity (zip (fun n => f1 (0 + n)) (fun n => f2 (0 + n)) (1 + 2 * n)).
  - apply zip_ext; intros; auto.
  - generalize 0 at 1 2 5 as k; induction n; auto; intros k.
    replace (1 + 2 * S n) with (S (S (1 + 2 * n))) by omega.
    unfold zip; fold (@zip X).
    replace (k + S n) with (S k + n) by omega.
    rewrite <-IHn.
    apply zip_ext; intros; f_equal; omega.
Qed.

Lemma finite_union_intersection {X Y} (A1 A2 : X -> Prop) (P : Y -> X -> Prop) :
  finite (fun y => exists x, A1 x /\ P y x) ->
  finite (fun y => exists x, A2 x /\ P y x) ->
  finite (fun y => exists x, (A1 x \/ A2 x) /\ P y x).
Proof.
  intros (n1 & f1 & H1).
  intros (n2 & f2 & H2).
  exists (2 * n1 + 1 + 2 * n2), (zip f1 f2).
  intros n (x & ([a1 | a2], Pnx)).
  - destruct (H1 n) as (i & ln & <-); eauto.
    exists (2 * i); split. omega. apply zip_1.
  - destruct (H2 n) as (i & ln & <-); eauto.
    exists (1 + 2 * i); split. omega. apply zip_2.
Qed.

Lemma finite_product:
  forall {A B}
    {PA : A -> Prop}
    {PB : B -> Prop},
    finite PA ->
    finite PB ->
    finite (fun ab => PA (fst ab) /\ PB (snd ab)).
Proof.
  intros A B PA PB [ NA [FA FA_spec]] [ NB [FB FB_spec]].
  exists (NB*NA)%nat.
  exists (fun n => ( FA (Nat.modulo n NA) , FB (Nat.div n NA))).
  intros [x1 x2] [PAx PBx].
  apply FA_spec in PAx. destruct PAx as [ia [ineqa funa]].
  apply FB_spec in PBx. destruct PBx as [ib [ineqb funb]].
  exists (ia + ib * NA); split.
  - replace (NB * NA) with (( 1 + ( NB - 1)) * NA).

    Focus 2.  f_equal.
    symmetry. apply le_plus_minus.
    apply lt_le_S.
    eapply Nat.le_lt_trans; eauto. omega.


    rewrite Nat.mul_add_distr_r.
    apply plus_lt_le_compat.
    omega.

    eapply mult_le_compat_r.
    omega.
  - f_equal.
    + rewrite Nat.mod_add.
      eapply Nat.mod_small_iff in ineqa.
      rewrite ineqa; auto.
      omega.
      omega.
    + rewrite Nat.div_add.
      eapply Nat.div_small_iff in ineqa.
      rewrite ineqa; auto.
      omega.
      omega.
Qed.

(* We have a simpler characterization of finite for subsets of nat  *)
Lemma finite_nat_bound A : @finite nat A <-> exists b, forall a, A a -> a < b.
Proof.
  split.
  - intros (c & f & Hf).
    pose (sumf := fix sum n := match n with O => O | S n => f n + sum n end).
    exists (1 + sumf c).
    intros x Ax; destruct (Hf x Ax) as (i & Hi & <-).
    replace c with (c - S i + S i) by omega.
    clear. generalize (c - S i); intros k.
    induction k; simpl; omega.
  - intros (b, Hb). exists b, id; intros x Ax; specialize (Hb x Ax); eauto.
Qed.

(* and a simpler proof for finite_union_intersection, too *)
Lemma finite_union_intersection_nat {X} (A1 A2 : X -> Prop) (P : nat -> X -> Prop) :
  finite (fun n => exists x, A1 x /\ P n x) ->
  finite (fun n => exists x, A2 x /\ P n x) ->
  finite (fun n => exists x, (A1 x \/ A2 x) /\ P n x).
Proof.
  repeat rewrite finite_nat_bound.
  intros (n1 & H1) (n2 & H2); exists (n1 + n2); intros a (x & m & p).
  cut (a < n1 \/ a < n2); [omega|].
  destruct m; eauto.
Qed.

Lemma not_infinite_finite A : (forall P, ~~P -> P) -> ~ infinite A <-> finite A.
Proof.
  intros ABS.
  split.
  - intros ninf; apply ABS; intros nfin.
    rewrite finite_nat_bound in nfin.
    assert (nfin' : forall b, exists a, ~(A a -> a < b)).
    + clear ninf. intros b; apply ABS; intros na.
      assert (forall a, ~(~(A a -> a < b))) by (intros a Ha; apply na; eauto).
      apply nfin. exists b; intros a. apply ABS; auto.
    + apply ninf; intros b. destruct (nfin' b) as (a, Ha).
      exists a; split.
      * cut (~ a < b); auto. omega.
      * apply ABS; tauto.
  - intros fin inf; apply finite_nat_bound in fin.
    destruct fin as (b & Hb).
    destruct (inf b) as (x & lx & Ax).
    specialize (Hb x Ax). omega.
Qed.

Lemma ramsey_inf_bin {X} (A1 A2 : X -> Prop) (P : nat -> X -> Prop) :
  (forall P, P \/ ~P) ->
  infinite (fun n => exists x, (A1 x \/ A2 x) /\ P n x) ->
  infinite (fun n => exists x, A1 x /\ P n x) \/
  infinite (fun n => exists x, A2 x /\ P n x).
Proof.
  intros EM inf.
  match goal with
    |- ?P \/ ?Q => cut (~(~P /\ ~Q)); [ generalize Q; generalize P; clear -EM | ]
  end.
  now intros P Q; destruct (EM (P \/ Q)); tauto.
  intros (n1, n2); revert inf.
  match goal with |- ?P -> _ => change (~P) end.
  rewrite EM_ABS in EM.
  rewrite not_infinite_finite in *; auto.
  apply finite_union_intersection; auto.
Qed.

Lemma ramsey_inf {X} (A : X -> Prop) (P : nat -> X -> Prop) :
  (forall P, P \/ ~P) ->
  finite A ->
  infinite (fun n => exists x, A x /\ P n x) ->
  exists x, A x /\ infinite (fun n => P n x).
Proof.
  intros EM (b & f & bound) inf.
  pose (An i := fun x => A x /\ f i = x).
  pose (Or := fix f i x := match i with O => False | S i => An i x \/ f i x end).
  assert (HA : forall x, A x <-> Or b x). {
    intros x; split.
    - intros Ax; destruct (bound x Ax) as (i & li & <-).
      replace b with (1 + (b - i - 1) + i) by omega.
      generalize (b - i - 1) as k; intros k.
      induction k.
      + compute; tauto.
      + simpl in *. tauto.
    - clear. induction b; compute; tauto.
  }

  clear bound.
  pattern A in inf |- *.
  match goal with |- ?P A => cut (P (Or b)) end.
  { intros (x, H); exists x. intuition. apply HA; auto. }
  match type of inf with ?P A => assert (inf' : P (Or b)) end.
  { intros a; destruct (inf a) as (c & ? & x & ?); exists c. intuition. exists x; intuition. rewrite <-HA; auto. }
  clear inf. simpl in inf'; rename inf' into inf. clear HA.

  induction b.
  - exfalso.
    destruct (inf 0) as (c & ? & x & INV & ?).
    inversion INV.
  - simpl in *.
    apply ramsey_inf_bin in inf; auto.
    destruct inf as [inf | inf].
    + exists (f b).
      destruct (inf 0) as (c & _ & x & (Anx & E) & _).
      split.
      * left. hnf. split; congruence.
      * intros a; destruct (inf a) as (d & ld & y & (Ay & Ey) & Pdy).
        exists d; split; auto. congruence.
    + specialize (IHb inf); destruct IHb.
      exists x. intuition.
Qed.

(** * Safety definitions *)

Section Safety.
  Definition rel X := X -> X -> Prop.

  Variable X : Type.
  Variable R : rel X.

  Inductive safeN : nat -> X -> Prop :=
  | safeO : forall x, safeN 0 x
  | safeS : forall n x x', R x x' -> safeN n x' -> safeN (S n) x.

  Definition safeN' n f : Prop := forall i, i < n -> R (f i) (f (1 + i)).

  (** Relating [safeN] to [safeN'] (everything is finite, no axioms) *)

  Lemma safeN_safeN' n x : safeN n x <-> (exists f, f 0 = x /\ safeN' n f).
  Proof with auto with *.
    split.
    - revert x; induction n; intros x Safe.
      + exists (fun _ => x); split; auto.
        inversion 1.
      + inversion Safe as [ | ? ? x' Step Safe']; subst.
        destruct (IHn x' Safe') as (f' & <- & IH).
        exists (fun n => match n with O => x | S n => f' n end).
        split; auto.
        intros [|i] Hi; simpl...
    - intros (f & <- & Sf).
      replace 0 with (n - n)...
      assert (L : n <= n)... revert L.
      generalize n at 1 3 5; intros i Hi; induction i. apply safeO.
      apply safeS with (f (n - i))...
      replace (n - i) with (1 + (n - S i))...
  Qed.

  (** Coinductive safety & corresponding Knaster-Tarski definition *)

  CoInductive safe : X -> Prop :=
    safe_cons : forall x x', R x x' -> safe x' -> safe x.

  Definition stable (P : X -> Prop) := forall x, P x -> exists x', R x x' /\ P x'.
  Definition kt_safe x := exists P, P x /\ stable P.

  Lemma kt_safe_safe x : safe x <-> kt_safe x.
  Proof.
    split; intros H.
    - exists safe; split; auto; clear.
      intros x H.
      inversion H; subst; eauto.
    - destruct H as (P & Px & SP).
      revert x Px; cofix CIH; intros x Px.
      destruct (SP x Px) as (x' & st & sa).
      apply (safe_cons x x' st).
      apply CIH, sa.
  Qed.

  (** Proving that [safe'] implies [safe] (the reverse implication
      only holds if we replace [f] with a coinductive stream) *)

  Definition safe' f := forall i, R (f i) (f (1 + i)).

  Lemma safe'_safe x : (exists f, f 0 = x /\ safe' f) -> safe x.
  Proof.
    intros (f & <- & Sf).
    generalize 0.
    cofix CIH; intros n.
    apply safe_cons with (f (1 + n)). apply Sf. apply CIH.
  Qed.

  (** From [safe], we can derive a function assumming the functional
      axiom of choice (but we don't need choice to prove [safe]) *)

  Lemma safe_safe' x :
    (forall P, P \/ ~P) ->
    FunctionalChoice ->
    safe x -> (exists f, f 0 = x /\ safe' f).
  Proof.
    intros EM FAC sa.
    rewrite kt_safe_safe in sa.
    destruct sa as (P & Px & HP).
    destruct (FAC _ _ (fun x y => P x -> R x y /\ P y)) as (f, Hf).
    - simpl. clear x Px.
      intros x.
      destruct (EM (P x)) as [p|np].
      + destruct (HP _ p). eauto.
      + exists x. tauto.
    - exists (fun n => Nat.iter n f x).
      split; auto.
      intro i.
      apply Hf.
      induction i; auto.
      simpl.
      apply Hf, IHi.
  Qed.

  Lemma not_ex_forall {A} (P : A -> Prop) : (~ex P) <-> (forall x, ~P x).
    split.
    - intros a x px; eauto.
    - intros a (x, px); apply (a x px).
  Qed.

  Lemma safeN_S n x : safeN (S n) x -> safeN n x.
  Proof.
    revert x; induction n. constructor.
    inversion 1; subst; econstructor; eauto.
  Qed.

  Lemma safeN_le n n' x : n <= n' -> safeN n' x -> safeN n x.
  Proof.
    intros l; replace n' with ((n' - n) + n) by omega.
    generalize (n' - n) as k; clear l; induction k; auto.
    intros H; apply IHk. apply safeN_S; auto.
  Qed.

  Lemma konigsafe x : (forall P, P \/ ~P) -> (forall x, finite (R x)) -> (forall n, safeN n x) -> safe x.
  Proof.
    intros EM FinBranching sa. apply kt_safe_safe.
    unfold kt_safe in *.
    pose proof EM as ABS; rewrite EM_ABS in ABS.
    apply ABS; intros nex.
    rewrite not_ex_forall in nex.
    apply (nex (fun x => forall n, safeN n x)).
    split. auto.
    clear x sa nex.
    intros x sa.
    pose proof @ramsey_inf _ (R x) safeN EM (FinBranching x) as Ramsey.
    assert_specialize Ramsey.
    {
      intros n; exists n; split. auto.
      specialize (sa (S n)).
      inversion sa; subst; eauto.
    }
    destruct Ramsey as (x' & st' & inf).
    exists x'; split; auto.
    intros n.
    destruct (inf n) as (n' & ln' & sa').
    eapply safeN_le; eauto.
  Qed.

End Safety.
