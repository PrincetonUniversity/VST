(*
 * Copyright (c) 2009-2010, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import msl.base.
Require Import msl.ageable.

Delimit Scope pred with pred.
Local Open Scope pred.

(* A "pre-predicate" is hereditary iff whenever it is
   true at world a, it is also true at all worlds
   accessable from a via R.
 *)
Definition hereditary {A} (R:A->A->Prop) (p:A->Prop) :=
  forall a a':A, R a a' -> p a -> p a'.

(* A predicate is a hereditary pre-predicate *)
Definition pred (A:Type) {AG:ageable A} :=
  { p:A -> Prop | hereditary age p }.

Bind Scope pred with pred.

(* Here is some junk that makes the definition of "pred" opaque
   to most tactics but sill allows the "Program" extension to
   see it is a subset type.  The coercion is sugar that allows us to use
   predicates easily.
 *)
Definition app_pred {A} `{ageable A} (p:pred A) : A -> Prop := proj1_sig p.
Definition pred_hereditary `{ageable} (p:pred A) := proj2_sig p.
Coercion app_pred : pred >-> Funclass.
Global Opaque pred.

Hint Resolve @pred_hereditary.

Lemma pred_nec_hereditary {A} `{ageable A} (p:pred A) :
  forall a a':A, necR a a' -> p a -> p a'.
Proof.
  intros.
  induction H0; auto.
  apply pred_hereditary with x; auto.
Qed.

Program Definition mkPred {A} `{ageable A} (p:A -> Prop) : pred A :=
  fun x => forall x', necR x x' -> p x'.
Next Obligation.
  repeat intro.
  apply H1.
  apply rt_trans with a'; auto.
  apply rt_step; auto.
Qed.

(* The semantic notion of entailment.
 *)
Definition derives {A} `{ageable A} (P Q:pred A) := forall a:A, P a -> Q a.
Implicit Arguments derives.

(* "valid" relations are those that commute with aging.  These
   relations are the ones that can be turned into modalities.
 *)
Definition valid_rel {A} `{ageable A} (R:relation A) : Prop :=
  commut A age R /\ commut A R age.

(* A modaility is a valid relation *)
Definition modality {A} `{ageable A} := { R:relation A | valid_rel R }.

(* More black magic to make the definition of modaility mostly opaque. *)
Definition app_mode {A} `{ageable A} (m:modality) : A -> A -> Prop := proj1_sig m.
Definition mode_valid {A} `{ageable A} (m:modality) := proj2_sig m.
Global Opaque modality.
Coercion app_mode : modality >-> Funclass.

(* commutivity facts for the basic relations *)

Lemma valid_rel_commut_later1 {A} `{ageable A} : forall R,
  valid_rel R ->
  commut A laterR R.
Proof.
  intros; hnf; intros.
  revert z H2.
  induction H1; intros.
  destruct H0.
  destruct (H0 _ _ H1 _ H2).
  exists x0; auto.
  apply t_step; auto.
  destruct (IHclos_trans1 _ H2).
  destruct (IHclos_trans2 _ H1).
  exists x1; auto.
  eapply t_trans; eauto.
Qed.

Lemma valid_rel_commut_later2 {A} `{ageable A} : forall R,
  valid_rel R ->
  commut A R laterR.
Proof.
  intros; hnf; intros.
  revert x H1.
  induction H2; intros.
  destruct H0.
  destruct (H3 _ _ H2 _ H1).
  exists x1; auto.
  apply t_step; auto.
  destruct (IHclos_trans2 _ H1).
  destruct (IHclos_trans1 _ H3).
  exists x2; auto.
  eapply t_trans; eauto.
Qed.

Lemma valid_rel_commut_nec1 {A} `{ageable A} : forall R,
  valid_rel R ->
  commut A necR R.
Proof.
  intros; hnf; intros.
  apply nec_refl_or_later in H1; destruct H1; subst.
  exists z; auto.
  destruct (valid_rel_commut_later1 R H0 x y H1 z H2).
  exists x0; auto.
  apply Rt_Rft; auto.
Qed.

Lemma valid_rel_commut_nec2 {A} `{ageable A} : forall R,
  valid_rel R ->
  commut A R necR.
Proof.
  intros; hnf; intros.
  apply nec_refl_or_later in H2; destruct H2; subst.
  exists x; auto.
  destruct (valid_rel_commut_later2 R H0 x y H1 z H2).
  exists x0; auto.
  apply Rt_Rft; auto.
Qed.

Lemma valid_rel_age {A} `{ageable A} : valid_rel age.
Proof.
  intros; split; hnf; intros; firstorder.
Qed.

Lemma valid_rel_later {A} `{ageable A} : valid_rel laterR.
Proof.
  intros; split; hnf; intros.
  revert x H0.
  induction H1; intros.
  exists y; auto.
  apply t_step; auto.
  destruct (IHclos_trans2 _ H0).
  destruct (IHclos_trans1 _ H2).
  exists x2; auto.
  eapply t_trans; eauto.

  revert z H1.
  induction H0; intros.
  exists x; auto.
  apply t_step; auto.
  destruct (IHclos_trans1 _ H1).
  destruct (IHclos_trans2 _ H0).
  exists x1; auto.
  eapply t_trans; eauto.
Qed.

Lemma valid_rel_nec {A} `{ageable A} : valid_rel necR.
Proof.
  intros; split; hnf; intros.
  revert x H0.
  induction H1; intros.
  exists y; auto.
  apply rt_step; auto.
  exists x0; auto.
  destruct (IHclos_refl_trans2 _ H0).
  destruct (IHclos_refl_trans1 _ H2).
  exists x2; auto.
  eapply rt_trans; eauto.

  revert z H1.
  induction H0; intros.
  exists x; auto.
  apply rt_step; auto.
  exists z; auto.

  destruct (IHclos_refl_trans1 _ H1).
  destruct (IHclos_refl_trans2 _ H0).
  exists x1; auto.
  eapply rt_trans; eauto.
Qed.

(* Definitions of the basic modalities.
 *)
Definition ageM {A} `{ageable A} : modality
  := exist _ age valid_rel_age.
Definition laterM {A} `{ageable A} : modality
  := exist _ laterR valid_rel_later.
(*
Definition necM {A} `{ageable A} : modality
  := exist _ necR valid_rel_nec.
*)

Hint Resolve rt_refl rt_trans t_trans.
Hint Unfold necR.
Obligation Tactic := unfold hereditary; intuition;
    first [eapply pred_hereditary; eauto; fail | eauto ].

(* Definitions of the basic propositional conectives.
 *)

(* Lifting pure mathematical facts to predicates *)

Program Definition prop {A} `{ageable A}  (P: Prop) : pred A := (fun _  => P).

Definition TT {A} `{ageable A}: pred A := prop True.
Definition FF  {A} `{ageable A}: pred A := prop False.

Program Definition imp {A} `{ageable A} (P Q:pred A) : pred A :=
   fun a:A => forall a':A, necR a a' -> P a' -> Q a'.
Next Obligation.
  apply H1; auto.
  apply rt_trans with a'; auto.
  apply rt_step; auto.
Qed.
Program Definition orp {A} `{ageable A} (P Q:pred A) : pred A :=
   fun a:A => P a \/ Q a.
Next Obligation.
  left; eapply pred_hereditary; eauto.
  right; eapply pred_hereditary; eauto.
Qed.

Program Definition andp {A} `{ageable A} (P Q:pred A) : pred A :=
   fun a:A => P a /\ Q a.

(* Universal and exp quantification
 *)

Program Definition allp {A} `{ageable A} {B: Type} (f: B -> pred A) : pred A
  := fun a => forall b, f b a.
Next Obligation.
  apply pred_hereditary with a; auto.
  apply H1.
Qed.

Program Definition exp {A} `{ageable A} {B: Type} (f: B -> pred A) : pred A
  := fun a => exists b, f b a.
Next Obligation.
  destruct H1; exists x; eapply pred_hereditary; eauto.
Qed.


(* Definition of the "box" modal operator.  This operator turns
   modalities (relations) into a "necessarily" type operator.
 *)

Program Definition box {A} `{ageable A} (M:modality) (P:pred A) : pred A :=
  fun a:A => forall a', M a a' -> P a'.
Next Obligation.
  destruct M as [M [H3 H4]]; simpl in *.
  destruct (H4 _ _ H2 _ H0).
  apply pred_hereditary with x; auto.
  apply H1; auto.
Qed.

(* Definition of the "diamond" modal operator.  This operator
   turns modalities into a "possibly" type operator.  _However_,
   note that this is NOT the boolean dual to "box", as usually
   found in accounts of modal logic. Instead, this is the
   "proof-theoretic" dual as found in Restall's "A Introduction
   to Substructural Logic" (2000).
 *)

Program Definition diamond {A} `{ageable A} (M:modality) (P:pred A) : pred A :=
  fun a:A => exists a', M a' a /\ P a'.
Next Obligation.
  destruct M as [M [H3 H4]]; simpl in *.
  destruct H1 as [x [? ?]].
  destruct (H3 _ _ H0 _ H1).
  exists x0; split; auto.
  apply pred_hereditary with x; auto.
Qed.

Definition boxy {A} `{ageable A} (m: modality) (p: pred A): Prop :=  box m p = p.

(* A pile of notations for the operators we have defined *)
Notation "P '|--' Q" := (derives P Q) (at level 80, no associativity).
Notation "'EX'  x ':' T ',' P " := (exp (fun x:T => P%pred)) (at level 65, x at level 99) : pred.
Notation "'ALL'  x ':' T  ',' P " := (allp (fun x:T => P%pred)) (at level 65, x at level 99) : pred.
Infix "||" := orp (at level 50, left associativity) : pred.
Infix "&&" := andp (at level 40, left associativity) : pred.
Notation "P '-->' Q" := (imp P Q) (at level 55, right associativity) : pred.
Notation "P '<-->' Q" := (andp (imp P Q) (imp Q P)) (at level 57, no associativity) : pred.
(* Notation "'[]' e" := (box necM e) (at level 30, right associativity): pred. *)
Notation "'|>' e" := (box laterM e) (at level 30, right associativity): pred.
Notation "'!!' e" := (prop e) (at level 25) : pred.

(* Rules for the propositional connectives *)
Lemma modus_ponens {A} `{ageable A} : forall (X P Q:pred A),
  X |-- P ->
  X |-- (P --> Q) ->
  X |-- Q.
Proof.
  unfold derives, imp; simpl; intuition eauto.
Qed.

Lemma andp_right {A} `{ageable A} : forall (X P Q:pred A),
  X |-- P ->
  X |-- Q ->
  X |-- P && Q.
Proof.
  unfold derives, imp, andp; simpl; intuition.
Qed.


  Lemma pred_ext' {A} `{ageable A}: forall (p1 p2:pred A),
    app_pred p1 = app_pred p2 ->
    p1 = p2.
  Proof.
    intros; destruct p1; destruct p2; simpl in H.
   simpl in H0. 
    subst x0.
    replace h0 with h by apply proof_irr.
    auto.
  Qed.

Lemma pred_ext : forall A `{ageable A} (P Q:pred A),
  derives P Q -> derives Q P -> P = Q.
Proof.
  intros.
  destruct P as [P HP].
  destruct Q as [Q HQ].
  unfold derives in *. simpl in *.
   apply (exist_ext (A->Prop) (fun p => hereditary (@age _ H) p)).
  extensionality a.
  apply prop_ext; intuition.
Qed.

Lemma andp_dup {A}{agA: ageable A}: forall P: pred A, P && P = P.
Proof. intros. apply pred_ext; intros w ?. destruct H; auto. split; auto.
Qed.

Lemma andp_left1{A}{agA: ageable A}: forall P Q R: pred A,  P |-- R -> P && Q |-- R.
Proof. repeat intro. destruct H0; auto.
Qed.

Lemma andp_left2{A}{agA: ageable A}: forall P Q R: pred A,  Q |-- R -> P && Q |-- R.
Proof. repeat intro. destruct H0; auto.
Qed.

Lemma orp_left{A}{agA: ageable A}: forall P Q R: pred A,  P |-- R -> Q |-- R -> P || Q |-- R.
Proof. repeat intro. destruct H1; auto.
Qed.

Lemma orp_right1{A}{agA: ageable A}: forall P Q R: pred A,  P |-- Q -> P |-- Q || R. 
Proof. repeat intro. left; auto.
Qed.

Lemma orp_right2{A}{agA: ageable A}: forall P Q R: pred A,  P |-- R -> P |-- Q || R. 
Proof. repeat intro. right; auto.
Qed.


Lemma derives_trans {A}`{ageable A}: 
    forall P Q R: pred A, P |-- Q -> Q |-- R -> P |-- R.
Proof. firstorder. Qed.

Lemma exp_right: 
  forall {B A: Type}{agA: ageable A}(x:B) p (q: B -> pred A),
    p |-- q x ->
    p |-- exp q.
Proof.
intros.
eapply derives_trans; try apply H.
intros w ?; exists x; auto.
Qed.

Lemma exp_left:
  forall {B A: Type}{agA: ageable A}(p: B -> pred A) q,
  (forall x, p x |-- q) ->
   exp p |-- q.
Proof.
intros.
intros w [x' ?].
eapply H; eauto.
Qed.

Lemma and1 {A} `{ageable A} : forall (X P Q:pred A),
  X |-- P && Q --> P.
Proof.
  unfold derives, imp, andp; simpl; intuition eauto.
Qed.

Lemma and2 {A} `{ageable A} : forall (X P Q:pred A),
  X |-- P && Q --> Q.
Proof.
  unfold derives, imp, andp; simpl; intuition eauto.
Qed.

Lemma and3 {A} `{ageable A} : forall (X P Q R:pred A),
  X |-- (P --> Q) --> (P --> R) --> (P --> Q && R).
Proof.
  unfold derives, imp, andp; simpl; intuition eauto.
Qed.

Lemma or1 {A} `{ageable A} : forall (X P Q:pred A),
  X |-- P --> P || Q.
Proof.
  unfold derives, imp, orp; simpl; intuition.
Qed.

Lemma or2 {A} `{ageable A} : forall (X P Q:pred A),
  X |-- Q --> P || Q.
Proof.
  unfold derives, imp, orp; simpl; intuition.
Qed.

Lemma or3 {A} `{ageable A} : forall (X P Q R:pred A),
  X |-- (P --> R) --> (Q --> R) --> (P || Q --> R).
Proof.
  unfold derives, imp, orp; simpl; intuition eauto.
Qed.

Lemma TTrule {A} `{ageable A} : forall X P,
  X |-- P --> TT.
Proof.
  unfold derives, imp, TT; simpl; intuition.
Qed.

Lemma FFrule {A} `{ageable A} : forall X P,
  X |-- FF --> P.
Proof.
  unfold derives, imp, FF; simpl; intuition.
Qed.

Lemma distribution {A} `{ageable A} : forall (X P Q R:pred A),
  X |-- P && (Q || R) --> (P && Q) || (P && R).
Proof.
  unfold derives, imp, orp, andp; simpl; intuition.
Qed.

(* Characterize the relation between conjunction and implication *)
Lemma imp_andp_adjoint {A} `{ageable A} : forall (P Q R:pred A),
  (P && Q) |-- R <-> P |-- (Q --> R).
Proof.
  split; intros.
  hnf; intros; simpl; intros.
  apply H0.
  split; auto.
  apply pred_nec_hereditary with a; auto.
  hnf; intros.
  hnf in H0.
  unfold imp in H0; simpl in H0.
  destruct H1.
  apply H0 with a; auto.
Qed.

(* Some facts about modalities *)

Lemma box_e0 {A} `{ageable A}: forall (M: modality) Q, 
            reflexive _ M -> box M Q  |-- Q.
Proof.
intros.
intro; intros.
apply H1; simpl.
apply H0.
Qed.
Implicit Arguments box_e0.

Lemma boxy_i {A} `{ageable A}: 
  forall (Q: pred A) (M: modality),
    reflexive _ M -> 
    (forall w w', M w w' -> Q w -> Q w') ->
    boxy M Q.
Proof.
intros.
unfold boxy.
apply pred_ext; hnf; intros.
eapply box_e0; eauto.
hnf; intros.
eapply H1; eauto.
Qed.

(*
Lemma necM_refl {A} `{ageable A}: reflexive _ necM.
Proof.
intros; intro; simpl.
unfold necR.
constructor 2.
Qed.

Hint Resolve @necM_refl.
*)

(* relationship between box and diamond *)
Lemma box_diamond {A} `{ageable A} : forall M (P Q:pred A),
  (diamond M P) |-- Q <-> P |-- (box M Q).
Proof.
  unfold derives; intuition.
  hnf; intros.
  apply H0.
  hnf; eauto.
  destruct H1 as [a' [? ?]].
  apply H0 with a'; auto.
Qed.

(* Box is a normal modal operator *)

Lemma ruleNec {A} `{ageable A} : forall M (P:pred A),
  derives TT P ->
  derives TT (box M P).
Proof.
  intros.
  rewrite <- box_diamond.
  hnf; intros.
  apply H0; hnf; auto.
Qed.

Lemma axiomK {A} `{ageable A}: forall M (P Q:pred A),
  (box M (P --> Q)) |-- (box M P --> box M Q).
Proof.
  intros; do 3 (hnf; intros).
  destruct M as [R HR]; simpl in *.
  destruct (valid_rel_commut_nec2 R HR _ _ H3 _ H1).
  apply H0 with x; auto.
Qed.

(* Box and diamond are positive modal operators *)

Lemma box_positive {A} `{ageable A} : forall M (P Q:pred A),
  P |-- Q ->
  box M P |-- box M Q.
Proof.
  unfold derives, box; simpl; intuition.
Qed.

Lemma diamond_positive {A} `{ageable A} : forall M (P Q:pred A),
  P |-- Q ->
  diamond M P |-- diamond M Q.
Proof.
  unfold derives, diamond; simpl; firstorder.
Qed.

Lemma box_refl_trans {A} `{ageable A}: forall (m:modality) p,
  reflexive _ m ->
  transitive _ m ->
  box m (box m p) = box m p.
Proof.
  intros.
  apply pred_ext.
  repeat intro.
  assert (box m p a').
  apply H2; auto.
  apply H4.
  apply H0.
  repeat intro.
  apply H2.
  eapply H1; eauto.
Qed.

(* Disribuitivity of box over various connectives *)

Lemma box_and {A} `{ageable A}: forall R (P Q:pred A),
  box R (P && Q) = box R P && box R Q.
Proof.
  intros; apply pred_ext; hnf; intuition;
    unfold andp, box in *; simpl in *; firstorder.
Qed.

Lemma box_all {A} `{ageable A} : forall B R (F:B -> pred A),
  box R (allp F) = ALL x:B, box R (F x).
Proof.
  intros; apply pred_ext; hnf; intuition;
    unfold allp, box in *; simpl in *; firstorder.
Qed.

Lemma box_ex {A} `{ageable A} : forall B R (F:B->pred A),
  EX x:B, box R (F x) |-- box R (exp F).
Proof.
  unfold derives, exp, box; simpl; firstorder.
Qed.

Lemma box_or {A} `{ageable A} : forall R (P Q:pred A),
   box R P || box R Q |-- box R (P || Q).
Proof.
  unfold derives, orp, box; simpl; firstorder.
Qed.

(* Distributivity of diamond over various operators *)

Lemma diamond_or {A} `{ageable A} : forall R (P Q:pred A),
  diamond R (P || Q) = diamond R P || diamond R Q.
Proof.
  intros; apply pred_ext; hnf; intuition;
    unfold diamond, orp in *; simpl in *; firstorder.
Qed.

Lemma diamond_ex {A} `{ageable A} : forall B R (F:B -> pred A),
  diamond R (exp F) = EX x:B, diamond R (F x).
Proof.
  intros; apply pred_ext; hnf; intuition;
    unfold diamond, exp in *; simpl in *; firstorder.
Qed.

Lemma diamond_and {A} `{ageable A} : forall R (P Q:pred A),
  diamond R (P && Q) |-- diamond R P && diamond R Q.
Proof.
  unfold derives, andp, diamond; simpl; firstorder.
Qed.

Lemma diamond_all {A} `{ageable A} : forall B R (F:B->pred A),
  diamond R (allp F) |-- ALL x:B, diamond R (F x).
Proof.
  unfold derives, allp, diamond; simpl; firstorder.
Qed.


(* Lemmas about aging and the later operator *)

(*
Lemma nec_useless {A} `{ageable A} :
  forall P, []P = P.
intros.
  apply pred_ext; intros.
  hnf; intros; apply H0.
  simpl; apply necM_refl.
  hnf; intros.
  hnf; intros.
  apply pred_nec_hereditary with a; auto.
Qed.
*)

Lemma later_age {A} `{ageable A} : forall P,
  |>P = box ageM P.
Proof.
  intros; apply pred_ext; do 2 (hnf; intros).
  simpl in H0.
  apply H0.
  apply t_step; auto.
  revert H0; induction H1; intros.
  apply H1; auto.
  apply pred_nec_hereditary with y.
  apply Rt_Rft; auto.
  apply IHclos_trans1; auto.
Qed.

Lemma now_later {A} `{ageable A} : forall P,
  P |-- |>P.
Proof.
  repeat intro.
  apply pred_nec_hereditary with a; auto.
  apply Rt_Rft; auto.
Qed.

Lemma now_later2 {A} `{ageable A} : forall G P,
  G |-- P ->
  G |-- |>P.
Proof.
  intros; apply @derives_trans with P; auto.
  apply now_later.
Qed.

(* The "induction" rule for later *)

Lemma goedel_loeb {A} `{ageable A} : forall (P Q:pred A),
  Q && |>P |-- P ->
  Q |-- P.
Proof.
  intros; hnf; intro a.
  induction a using age_induction.
  intros; simpl in H0.
  eapply H0; auto.
  split; auto.
  rewrite later_age.
  simpl; intros.
  apply H1; auto.
  apply pred_hereditary with x; auto.
Qed.

Lemma loeb {A} `{ageable A} : forall (P Q:pred A),
     |>P |-- P    ->     TT |-- P.
Proof.
  intros. apply goedel_loeb.
  apply andp_left2. auto.
Qed.

(* Later distributes over almost everything! *)

Lemma later_commute_dia {A} `{ageable A} : forall M (P:pred A),
  diamond M (|> P) |-- |> (diamond M P).
Proof.
  intros.
  repeat rewrite later_age.
  do 3 (hnf; intros).
  simpl in H0.
  firstorder.
  destruct M as [R HR].
  simpl in *.
  destruct HR.
  destruct (H3 _ _ H1 _ H0).
  exists x0; split; auto.
Qed.

Lemma later_commute {A} `{ageable A} : forall M (P:pred A),
  box M (|>P) = |>(box M P).
Proof.
  intros.
  apply pred_ext; do 3 (hnf; intros).
  destruct M as [R HR].
  destruct (valid_rel_commut_later2 R HR _ _ H2 _ H1).
  apply H0 with x; simpl; auto.
  destruct M as [R HR].
  destruct (valid_rel_commut_later1 R HR _ _ H2 _ H1).
  apply H0 with x; auto.
Qed.

Lemma later_and {A} `{ageable A} : forall P Q,
  |>(P && Q) = |>P && |> Q.
Proof.
  intros; apply box_and.
Qed.

Lemma later_or {A} `{ageable A} : forall (P Q:pred A),
  |>(P || Q) = |>P || |>Q.
Proof.
  intros.
  repeat rewrite later_age.
  apply pred_ext.
  2: apply box_or.
  hnf; intros.
  simpl in H0.
  case_eq (age1 a); intros.
  destruct (H0 a0); auto.
  left; simpl; intros.
  replace a' with a0; auto.
  congruence.
  right; simpl; intros.
  replace a' with a0; auto.
  congruence.
  left.
  hnf; simpl; intros.
  hnf in H2.
  rewrite H1 in H2; discriminate.
Qed.

Lemma later_ex {A} `{ageable A} : forall B (F:B->pred A),
  B ->
  |>(exp F) = EX x:B, |>(F x).
Proof.
  intros.
  apply pred_ext.
  2: apply box_ex.
  hnf; intros.
  rewrite later_age in H0.
  case_eq (age1 a); intros.
  destruct (H0 a0); auto.
  exists x.
  rewrite later_age; simpl; intros.
  replace a' with a0; auto.
  congruence.
  exists X.
  rewrite later_age.
  hnf; simpl; intros.
  unfold age in H2.
  rewrite H1 in H2; discriminate.
Qed.

Lemma later_imp {A} `{ageable A} : forall P Q,
  |>(P --> Q) = |>P --> |>Q.
Proof.
  intros; repeat rewrite later_age.
  apply pred_ext.
  apply axiomK.
  hnf; intros.
  simpl; intros.
  simpl in H0.
  destruct valid_rel_nec.
  destruct (H5 _ _ H2 _ H1).
  apply H0 with x; auto.
  intros.
  replace a'1 with a'0; auto.
  congruence.
Qed.

Lemma TT_boxy {A} `{ageable A} : forall M,
  boxy M TT.
Proof.
  intros; hnf.
  apply pred_ext; repeat intro; simpl; auto.
Qed.

Lemma positive_boxy {A} `{ageable A} : forall P Q M,
  boxy M P ->
  P |-- Q ->
  P |-- box M Q.
Proof.
  intros.
  rewrite <- H0.
  apply box_positive.
  auto.
Qed.

Lemma forallI {A} `{ageable A} : forall A G X,
  (forall x:A, G |-- X x) ->
  G |-- allp X.
Proof.
  repeat intro.
  eapply H0; auto.
Qed.

Lemma TT_and {A} `{ageable A} : forall P,
  TT && P = P.
Proof.
  intros; apply pred_ext; repeat intro.
  destruct H0; auto.
  split; simpl; auto.
Qed.

Lemma andp_comm {A} `{ageable A} : forall P Q,
  P && Q = Q && P.
Proof.
  intros; apply pred_ext; unfold andp; repeat intro; simpl in *; intuition.
Qed.

Lemma andp_assoc {A} `{ageable A} : forall P Q R,
  (P && Q) && R = P && (Q && R).
Proof.
  intros; apply pred_ext; auto; unfold derives, andp; simpl; intuition.
Qed.

Lemma ex_and : forall {A} `{ageable A} B (P:B->pred A) Q,
  (exp P) && Q = EX x:B, P x && Q.
Proof.
  intros. apply pred_ext.
  repeat intro. destruct H0. destruct H0.
  exists x. split; auto.
  repeat intro.
  destruct H0. destruct H0.
  split; auto. exists x; auto.
Qed.

Lemma FF_and : forall {A} `{ageable A} (P:pred A),
  FF && P = FF.
Proof.
  intros. apply pred_ext; repeat intro.
  destruct H0; auto.
  elim H0.
Qed.


Lemma boxy_e {A} `{H : ageable A}: forall (M: modality) P,  boxy M P -> 
           forall w w', app_mode M w w' -> P w -> P w'.
Proof.
intros.
rewrite <- H0 in H2; eauto.
Qed.

Lemma boxy_andp {A} `{H : ageable A}: 
     forall (M: modality) , reflexive _ (app_mode M) -> 
      forall P Q, boxy M P -> boxy M Q -> boxy M (P && Q).
Proof.
destruct M; 
intros.
simpl in *.
apply boxy_i; intros; auto.
destruct H4.
simpl.
split; eapply boxy_e; eauto.
Qed.

Hint Resolve @boxy_andp.

Lemma boxy_disjunction {A} `{H : ageable A}: 
     forall (M: modality) , reflexive _ (app_mode M) -> 
      forall P Q, boxy M P -> boxy M Q -> boxy M (P || Q).
Proof.
destruct M; 
intros.
simpl in *.
apply boxy_i; intros; auto.
destruct H4.
left.  eapply boxy_e; eauto.
right. eapply boxy_e; eauto.
Qed.

Hint Resolve @boxy_disjunction.

Lemma boxy_exp {A} `{agA : ageable A}:
    forall (M: modality) T (P: T -> pred A), 
     reflexive _ (app_mode M) ->
     (forall x, boxy M (P x)) -> boxy M (exp P).
Proof.
intros.
apply boxy_i; auto; intros.
destruct H2 as [x ?].
rewrite <- H0 in H2.
spec H2 w' H1.
econstructor; eauto.
Qed.

Hint Resolve @boxy_exp.

Lemma boxy_prop {A} `{H : ageable A}:  forall (M: modality) P, reflexive _ (app_mode M) -> boxy M (prop P).
Proof.
intros.
apply boxy_i; auto.
Qed.

Lemma boxy_TT {A} `{H : ageable A}:  forall (M: modality), reflexive _ (app_mode M) -> boxy M TT.
Proof. 
intros.
apply boxy_i; intros; auto.
Qed.

Lemma boxy_FF {A} `{H : ageable A}:  forall (M: modality), reflexive _ (app_mode M) -> boxy M FF.
Proof.
intros; apply boxy_i; intros; auto; contradiction.
Qed.

Hint Resolve @boxy_TT.
Hint Resolve @boxy_FF.

Lemma TT_i  {A} `{ageable A}: forall w: A,  app_pred TT w.
Proof.
unfold TT, prop; simpl; auto.
Qed.

Hint Resolve @TT_i.

Lemma prop_andp_left {A}{agA: ageable A}: forall (P: Prop) Q R, (P -> Q |-- R) -> !!P && Q |-- R.
Proof.
 repeat intro. destruct H0; auto. apply H; auto.
Qed.

Lemma prop_andp_right {A}{agA: ageable A}: forall (P: Prop) Q R, P -> Q |-- R -> Q |-- !!P && R.
Proof.
 repeat intro. split; auto.
Qed.

Lemma prop_true_andp:
  forall (P: Prop) A `{ageable A} (Q: pred A), P -> (!! P && Q = Q).
Proof.
intros.
apply pred_ext.
unfold derives; intros ? [? ?]; auto.
unfold derives; intros; split; auto.
Qed.

Lemma prop_andp_e {A} `{ageable A}:  forall P Q (w:A), (!! P && Q) w -> P /\ Q w.
Proof.
intuition; destruct H0; auto.
Qed.

Lemma prop_andp_i {A} `{ageable A}:  forall P Q (w:A), P /\ app_pred Q w -> (!! P && Q) w.
Proof.
intuition.
split; auto.
Qed.

Lemma later_derives {A} `{agA : ageable A}: forall {P Q}, (P |-- Q) -> (|> P |-- |> Q).
Proof.
unfold derives; intros.
intro; intros; eapply H.
eauto.
Qed.

Lemma boxy_allp {A} `{agA : ageable A}:
  forall (M: modality) (B: Type) F, 
     reflexive _ (app_mode M) ->
     (forall (x:B), boxy M (F x)) -> boxy M (allp F).
Proof.
intros.
destruct M as [R V].
simpl in *.
apply boxy_i; auto.
intros.
simpl in *.
intro.
spec H2 b.
rewrite <- H0 in H2.
apply H2; auto.
Qed.
Hint Resolve @boxy_allp.

Lemma later_allp {A} `{agA : ageable A}:  
       forall B P, |> (allp P) = allp (fun x:B => |> (P x)).
Proof.
intros.
apply pred_ext; unfold derives; simpl; intros; eapply H; eauto.
Qed.

Lemma box_derives {A} `{ageable A} : forall M (P Q:pred A),
  P |-- Q ->  box M P |-- box M Q.
Proof. exact box_positive. Qed.

Lemma allp_derives: 
       forall {A: Type} `{agA: ageable A} (B: Type) (P Q: B -> pred A), 
               (forall x:B, P x |-- Q x) -> (allp P |-- allp Q).
Proof.
intros.
intros w b ?.
eapply H; eauto.
Qed.

Lemma forall_pred_ext  {A} `{agA : ageable A}: forall B (P Q: B -> pred A), 
 (ALL x : B, (P x <--> Q x)) |-- (ALL x : B, P x) <--> (ALL x: B, Q x) .
Proof.
intros.
intros w ?.
split; intros ? ? ? ?;  destruct (H b); eauto.
Qed.

Lemma exists_pred_ext  {A} `{agA : ageable A}: forall B (P Q: B -> pred A), 
 (ALL x : B, (P x <--> Q x)) |-- (EX x : B, P x) <--> (EX x: B, Q x) .
Proof.
intros.
intros w ?.
split; intros w' ? [? ?]; exists x; eapply H; eauto.
Qed.

Lemma imp_pred_ext  {A} `{agA : ageable A}: forall B B' P Q, 
       (B <--> B') && (B --> (P <--> Q)) 
 |-- (B --> P) <-->  (B' --> Q).
Proof.
intros.
intros w [? ?].
split; intros w'' ? ? w3 ? ?.
eapply H0.
4: eapply H2; eauto.
2: eapply H; try apply H4.
econstructor 3; eauto.
econstructor 3; eauto.
constructor 2.
eapply H; eauto.
eapply H0.
4: eapply H2; eauto.
2: eapply H; try apply H4.
econstructor 3; eauto.
econstructor 3; eauto.
eapply H; eauto.
econstructor 3; eauto.
eapply H; eauto.
Qed.

Lemma derives_refl {A: Type} `{ageable A}:
  forall (P: pred A), (P |-- P).
Proof. firstorder.
Qed.

Hint Resolve @derives_refl.

Lemma andp_derives {A} `{ageable A}:
  forall P Q P' Q': pred A, P |-- P' -> Q |-- Q' -> P && Q |-- P' && Q'.
Proof.
intros.
intros w [? ?]; split; auto.
Qed.

Lemma orp_derives {A} `{ageable A}:
  forall P Q P' Q': pred A, P |-- P' -> Q |-- Q' -> P || Q |-- P' || Q'.
Proof.
intros.
 apply orp_left. apply orp_right1; auto. apply orp_right2; auto.
Qed.

Lemma exp_derives {A} `{HA : ageable A}: 
       forall B (P: B -> pred A) Q , (forall x:B, P x |-- Q x) -> (exp P |-- exp Q).
Proof.
intros.
intros w [b ?].
exists b; eapply H; eauto.
Qed.

Lemma box_ext {A} `{agA : ageable A}: forall (M: modality) P Q,
    box M (P <--> Q) |--  box M P <--> box M Q.
Proof.
intros.
repeat rewrite box_and.
apply andp_right;
eapply derives_trans; try apply axiomK; intros ? [? ?]; auto.
Qed.

Lemma andp_pred_ext {A} `{agA : ageable A}: forall P Q P' Q',
       (P <--> P') && (Q <--> Q') |--  (P && Q) <--> (P' && Q').
Proof.
intros.
intros w [? ?].
split; (intros w' ? [? ?]; split; [eapply H; eauto | eapply H0; eauto]).
Qed.

Program Definition exactly {A} `{ageable A} (x: A) : pred A := necR x.
Next Obligation.
constructor 3 with a; auto.
constructor 1; auto.
Qed.

Lemma derives_TT {A} `{ageable A}: forall (P: pred A), P |-- TT.
Proof.
intros.
intros ? ?; auto.
Qed.
Hint Resolve @derives_TT.

Lemma FF_derives {A} `{ageable A}: forall P, FF |-- P.
Proof.
intros. intros ? ?. hnf in H0; contradiction. 
Qed.
Hint Immediate @FF_derives.

Lemma necR_level' {A} `{H : ageable A}: forall {w w': A}, necR w w' -> 
       @necR _ ag_nat (level w) (level w').
Proof.
induction 1; simpl; intros.
apply age_level in H0. constructor 1.  unfold age, age1; simpl.  rewrite H0; reflexivity.
constructor 2.
constructor 3 with (level y); auto.
Qed.

Lemma derives_imp {A} `{agA : ageable A}:
  forall P Q w, (P |-- Q) -> (P --> Q) w.
Proof.
intros.
intros ? _; auto.
Qed.

Lemma exp_andp1 {A} `{ageable A}:
 forall B (p: B -> pred A) q, (exp p && q)%pred = (exp (fun x => p x && q))%pred.
Proof.
intros; apply pred_ext; intros w ?.
destruct H0.
destruct H0.
exists x; split; auto.
destruct H0. destruct H0.
split; auto.
exists x; auto.
Qed.

Lemma exp_andp2 {A} `{HA: ageable A}:
 forall B p (q: B -> pred A), (p && exp q)%pred = (exp (fun x => p && q x))%pred.
Proof.
intros; apply pred_ext; intros w ?.
destruct H.
destruct H0.
exists x; split; auto.
destruct H. destruct H.
split; auto.
exists x; auto.
Qed.

Lemma exp_imp_left {A} `{agA : ageable A}:  forall B (p: B -> pred A) q,
     (exp p --> q)%pred = allp (fun x => p x --> q)%pred.
Proof.
intros; apply pred_ext; intros w ?.
intro.
intros ?w ? ?.
eapply H.
apply necR_trans with w0; auto.
exists b; auto.
intros ?w ? [? ?].
eapply H; eauto.
Qed.

Lemma app_ext  {A: Type} `{ageable A} : forall (F G: A -> Prop) p1 p2 w, 
         (F w = G w) ->
         app_pred (exist (hereditary age) F p1) w = app_pred (exist (hereditary age) G p2) w.
Proof.
simpl; auto.
Qed.

Lemma imp_derives {A} `{agA : ageable A}:
  forall P P' Q Q',
    P' |-- P ->
    Q |-- Q' -> 
    P --> Q |-- P' --> Q'.
Proof.
intros.
intros w ? w'' ? ?.
apply H0.
eapply H1; eauto.
Qed.


Lemma imp_lem0  {A} `{agA : ageable A}:  forall P st, (TT --> P) st -> P st.
Proof.
intros; eauto.
Qed.

Lemma conjoin_hyp0  {A} `{H : ageable A}: 
      forall (P Q: pred A) w,  P w -> (P --> Q) w -> (TT --> Q) w.
Proof. 
intros.
intros w' ? ?.
eapply H1; 
eauto.
eapply pred_nec_hereditary; eauto.
Qed.

Lemma conjoin_hyp1 {A} `{agA : ageable A}: forall (P Q R: pred A)  w, 
            P w -> (P&&Q --> R) w -> (Q --> R) w.
Proof.
intros.
intros w' ? ?.
eapply H0; auto.
split; eauto.
eapply pred_nec_hereditary; eauto.
Qed.

Lemma derives_e {A: Type} `{agA : ageable A}: forall p q (st: A),
      (p |-- q) -> p st -> q st.
Proof.
auto.
Qed.

Ltac slurp :=
 apply imp_lem0; 
  match goal with |-  app_pred (_ --> _)  ?st => 
        repeat match goal with
                   | H: app_pred ?P st |- app_pred (?b --> ?c) st => 
                       (apply (@conjoin_hyp0 _ _ P c st H) ||
                        (apply (@conjoin_hyp1 _ _ P b c st H))); 
                       clear H
                   end;
        try (revert st; apply derives_e)
  end.

Lemma test_slurp {A} `{agA : ageable A} :  forall  (P Q R S : pred A) w , 
        (P && (Q && R) --> S) w -> P w -> Q w -> R w -> S w.
Proof.
intros.
remember (app_pred (P && (Q && R) --> S) w) as hide. 
slurp.
subst hide. assumption.
Qed.

Lemma later_andp {A} `{H : ageable A}:
  forall P Q, |> (P && Q) = |>P && |>Q.
Proof.
intros.
apply pred_ext; intros w ?.
split; intros w' ?; destruct (H0 _ H1); auto.
destruct H0.
intros w' ?; split; eauto.
Qed.

Lemma True_andp_eq {A}`{ageable A}:
  forall (P: Prop) (Q: pred A), P -> (!!P && Q)%pred = Q.
intros.
apply pred_ext; intros w ?; hnf in *; simpl; intros; intuition.
Qed.

Lemma distrib_orp_andp {A}{agA: ageable A}: 
   forall P Q R, (P||Q)&&R = (P&&R)||(Q&&R).
Proof.
  intros. apply pred_ext.
  intros w [[?|?] ?]; [left|right]; split; auto.
  intros w [[? ?]|[? ?]]; split; auto. left; auto. right; auto.
Qed.

Lemma allp_right {B A: Type}{agA: ageable A}:
  forall (P: pred A) (Q: B -> pred A),
  (forall v, P |-- Q v) ->
   P |-- allp Q.
Proof.
 intros. intros w ? v; apply (H v); auto.
Qed.

Lemma allp_left {B}{A}{agA: ageable A}: 
   forall (P: B -> pred A) x Q, P x |-- Q -> allp P |-- Q.
 Proof.
   intros. intros ? ?. apply H. apply H0.
Qed.

Lemma later_imp2 {A}{agA: ageable A}: forall P Q: pred A,
                 |> (P <--> Q) = |> P <--> |> Q.
Proof.
 intros.
  repeat rewrite <- later_imp. rewrite <- later_andp; auto.
Qed.
