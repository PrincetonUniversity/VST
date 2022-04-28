(*
 * Copyright (c) 2009-2010, Andrew Appel, Robert Dockins and Aquinas Hobor.
 *
 *)

Require Import VST.msl.base.
Require Import VST.msl.ageable.
Require Import RelationClasses.

Declare Scope pred.
Delimit Scope pred with pred.
Local Open Scope pred.

(* A "pre-predicate" is hereditary iff whenever it is
   true at world a, it is also true at all worlds
   accessable from a via R.
 *)
Definition hereditary {A} (R:A->A->Prop) (p:A->Prop) :=
  forall a a':A, R a a' -> p a -> p a'.

(* Following the ordered RA approach of "MoSeL: A General, Extensible Modal Framework for
   Interactive Proofs in Separation Logic", Krebbers et al.,
   our algebra is equipped with an order, and predicates must be
   upward-closed w.r.t. that order. In VeriC, this order is
   "adding more ghost state".
   Most importantly, "emp" will be true of anything above the empty element
   in this order. *)
Class Ext_ord (A : Type) {AG : ageable A} :=
  { ext_order : relation A;
    ext_preorder :> PreOrder ext_order;
(*    ext_age_commut : commut A ext_order age;*)
    (* This may not be true, since non-ordered elements may age to ordered elements *)
    age_ext_commut : commut A age ext_order;
    ext_age_compat : forall a b a', ext_order a b -> age a a' -> exists b', age b b' /\ ext_order a' b';
    ext_level : forall a b, ext_order a b -> level a = level b
  }.

Lemma ext_refl : forall `{Ext_ord} a, ext_order a a.
Proof.
  reflexivity.
Qed.

#[export] Hint Resolve ext_refl : core.

#[export] Program Instance Ext_prod A B `(Ext_ord A) (relB : relation B) {P : PreOrder relB} : @Ext_ord (A * B) (ag_prod A B _) :=
  { ext_order := fun a b => ext_order (fst a) (fst b) /\ relB (snd a) (snd b) }.
Next Obligation.
Proof.
  split.
  - intros (?, ?); split; reflexivity.
  - intros (?, ?) (?, ?) (?, ?) [] []; split; etransitivity; eauto.
Qed.
(*Next Obligation.
Proof.
  intros (?, ?) (?, ?) [] (?, ?) Hage.
  hnf in Hage; simpl in Hage.
  destruct (age1 a1) eqn: Hage1; [|discriminate].
  inv Hage.
  eapply ext_age_commut in Hage1 as [? Hage]; eauto.
  eexists (_, _); hnf; simpl; eauto.
  rewrite Hage; auto.
Qed.*)
Next Obligation.
Proof.
  intros (?, ?) (?, ?) Hage (?, ?) [].
  simpl in *.
  hnf in Hage; simpl in Hage.
  destruct (age1 a0) eqn: Hage1; [|discriminate].
  inv Hage.
  eapply age_ext_commut in Hage1 as [? ? Hage]; eauto.
  eexists (_, _); hnf; simpl; eauto.
  rewrite Hage; auto.
Qed.
Next Obligation.
Proof.
  simpl in *.
  hnf in H1; simpl in H1.
  destruct (age1 a) eqn: Hage1; [|discriminate].
  inv H1.
  eapply ext_age_compat in H0 as (? & Hage & ?); eauto.
  eexists (_, _); split; hnf; simpl; eauto.
  rewrite Hage; auto.
Qed.
Next Obligation.
Proof.
  simpl in *.
  eapply ext_level; eauto.
Qed.

Section Order.

Context {A : Type} {AG : ageable A}.
Context {EO : Ext_ord A}.


(* A predicate is a hereditary pre-predicate that is upward-closed
   according to the extension order. *)
Definition pred := { p:A -> Prop | hereditary age p /\ hereditary ext_order p }.

Bind Scope pred with pred.

(* Here is some junk that makes the definition of "pred" opaque
   to most tactics but still allows the "Program" extension to
   see it is a subset type.  The coercion is sugar that allows us to use
   predicates easily.
 *)
Definition app_pred (p:pred) : A -> Prop := proj1_sig p.
Definition pred_hereditary (p:pred) := proj1 (proj2_sig p).
Definition pred_upclosed (p:pred) := proj2 (proj2_sig p).
Coercion app_pred : pred >-> Funclass.
Global Opaque pred.

#[local] Hint Resolve pred_hereditary : core.

Lemma nec_hereditary (p: A -> Prop) : hereditary age p ->
  forall a a':A, necR a a' -> p a -> p a'.
Proof.
  intros.
  induction H0; auto.
  apply H with x; auto.
Qed.

Lemma pred_nec_hereditary (p:pred) :
  forall a a':A, necR a a' -> p a -> p a'.
Proof.
  apply nec_hereditary, pred_hereditary.
Qed.

(*Lemma ext_later_commut : commut A ext_order laterR.
Proof.
  repeat intro.
  revert dependent x; induction H0; intros.
  - eapply ext_age_commut in H as []; eauto.
    eexists; [|apply H1].
    apply t_step; auto.
  - apply IHclos_trans2 in H as [? ? Hext].
    apply IHclos_trans1 in Hext as [? ? Hext].
    eexists; [|apply Hext].
    eapply t_trans; eauto.
Qed.

Lemma ext_nec_commut : commut A ext_order necR.
Proof.
  repeat intro.
  apply nec_refl_or_later in H0 as [|]; subst; eauto.
  destruct (ext_later_commut _ _ H _ H0).
  eexists; [|apply H2].
  apply laterR_necR; auto.
Qed.*)

Lemma later_ext_commut : commut A laterR ext_order.
Proof.
  repeat intro.
  revert dependent z; induction H; intros.
  - eapply age_ext_commut in H as []; eauto.
    eexists; [apply H|].
    apply t_step; auto.
  - apply IHclos_trans1 in H1 as [? Hext ?].
    apply IHclos_trans2 in Hext as [? Hext ?].
    eexists; [apply Hext|].
    eapply t_trans; eauto.
Qed.

Lemma nec_ext_commut : commut A necR ext_order.
Proof.
  repeat intro.
  apply nec_refl_or_later in H as [|]; subst; eauto.
  destruct (later_ext_commut _ _ H _ H0).
  eexists; [apply H1|].
  apply laterR_necR; auto.
Qed.

Program Definition mkPred (p:A -> Prop) : pred :=
  fun x => forall x' x'', necR x x' -> ext_order x' x'' -> p x''.
Next Obligation.
  split; repeat intro.
  - eapply H0, H2.
    apply rt_trans with a'; auto.
    apply rt_step; auto.
  - eapply nec_ext_commut in H as [? ? ?]; [|apply H1].
    eapply H0; eauto.
    etransitivity; eauto.
Qed.

(* The semantic notion of entailment.
 *)
Definition derives (P Q:pred) := forall a:A, P a -> Q a.

(* "valid" relations are those that commute with aging and extension.
   These relations are the ones that can be turned into modalities.
 *)
Definition valid_rel (R:relation A) : Prop :=
  commut A age R /\ commut A R age /\ commut A R ext_order (*/\ commut A ext_order R*).

(* A modality is a valid relation *)
Definition modality := { R:relation A | valid_rel R }.

(* More black magic to make the definition of modality mostly opaque. *)
Definition app_mode (m:modality) : A -> A -> Prop := proj1_sig m.
Definition mode_valid (m:modality) := proj2_sig m.
Global Opaque modality.
Coercion app_mode : modality >-> Funclass.

(* commutivity facts for the basic relations *)

Lemma valid_rel_commut_later1 : forall R,
  valid_rel R ->
  commut A laterR R.
Proof.
  intros; hnf; intros.
  revert z H1.
  induction H0; intros.
  destruct H.
  destruct (H _ _ H0 _ H1).
  exists x0; auto.
  apply t_step; auto.
  destruct (IHclos_trans1 _ H1).
  destruct (IHclos_trans2 _ H0).
  exists x1; auto.
  eapply t_trans; eauto.
Qed.

Lemma valid_rel_commut_later2 : forall R,
  valid_rel R ->
  commut A R laterR.
Proof.
  intros; hnf; intros.
  revert x H0.
  induction H1; intros.
  destruct H as (_ & H & _).
  destruct (H _ _ H1 _ H0).
  exists x1; auto.
  apply t_step; auto.
  destruct (IHclos_trans2 _ H0).
  destruct (IHclos_trans1 _ H2).
  exists x2; auto.
  eapply t_trans; eauto.
Qed.

Lemma valid_rel_commut_nec1 : forall R,
  valid_rel R ->
  commut A necR R.
Proof.
  intros; hnf; intros.
  apply nec_refl_or_later in H0; destruct H0; subst.
  exists z; auto.
  destruct (valid_rel_commut_later1 R H x y H0 z H1).
  exists x0; auto.
  apply Rt_Rft; auto.
Qed.

Lemma valid_rel_commut_nec2 : forall R,
  valid_rel R ->
  commut A R necR.
Proof.
  intros; hnf; intros.
  apply nec_refl_or_later in H1; destruct H1; subst.
  exists x; auto.
  destruct (valid_rel_commut_later2 R H x y H0 z H1).
  exists x0; auto.
  apply Rt_Rft; auto.
Qed.

(*Lemma valid_rel_commut_ext1 : forall R,
  valid_rel R ->
  commut A ext_order R.
Proof.
  intros ? H; apply H.
Qed.*)

Lemma valid_rel_commut_ext2 : forall R,
  valid_rel R ->
  commut A R ext_order.
Proof.
  intros ? H; apply H.
Qed.

Lemma valid_rel_age : valid_rel age.
Proof.
  intros; split; hnf; intros; eauto.
  split; [|(*split; [*)apply age_ext_commut (*| apply ext_age_commut]*)].
  unfold commut; eauto.
Qed.

Lemma valid_rel_later : valid_rel laterR.
Proof.
  intros; split; hnf; intros.
  revert dependent x.
  induction H0; intros.
  exists y; auto.
  apply t_step; auto.
  destruct (IHclos_trans2 _ H).
  destruct (IHclos_trans1 _ H1).
  exists x2; auto.
  eapply t_trans; eauto.

  split; [|(*split; [*)apply later_ext_commut (*| apply ext_later_commut]*)].
  intros ???.
  induction H; intros.
  exists x; auto.
  apply t_step; auto.
  destruct (IHclos_trans1 _ H1).
  destruct (IHclos_trans2 _ H2).
  exists x1; auto.
  eapply t_trans; eauto.
Qed.

Lemma valid_rel_nec : valid_rel necR.
Proof.
  intros; split; hnf; intros.
  revert dependent x.
  induction H0; intros.
  exists y; auto.
  apply rt_step; auto.
  exists x0; auto.
  destruct (IHclos_refl_trans2 _ H).
  destruct (IHclos_refl_trans1 _ H1).
  exists x2; auto.
  eapply rt_trans; eauto.

  split; [|(*split; [*)apply nec_ext_commut (*| apply ext_nec_commut]*)].
  intros ???.
  induction H; intros.
  exists x; auto.
  apply rt_step; auto.
  exists z; auto.

  destruct (IHclos_refl_trans1 _ H1).
  destruct (IHclos_refl_trans2 _ H2).
  exists x1; auto.
  eapply rt_trans; eauto.
Qed.

(* Definitions of the basic modalities.
 *)
Definition ageM : modality
  := exist _ age valid_rel_age.
Definition laterM : modality
  := exist _ laterR valid_rel_later.
(*
Definition necM  : modality
  := exist _ necR valid_rel_nec.
*)

#[local] Hint Resolve rt_refl rt_trans t_trans : core.
#[local] Hint Unfold necR : core.
Obligation Tactic := unfold hereditary; intuition;
    first [eapply pred_hereditary; eauto; fail | eapply pred_upclosed; eauto; fail | eauto ].

(* Definitions of the basic propositional conectives.
 *)

(* Lifting pure mathematical facts to predicates *)

Program Definition prop (P: Prop) : pred := (fun _  => P).

Definition TT : pred := prop True.
Definition FF  : pred := prop False.

Program Definition imp  (P Q:pred) : pred :=
   fun a:A => forall a' a'':A, necR a a' -> ext_order a' a'' -> P a'' -> Q a''.
Next Obligation.
  apply H0 with a'0; auto.
  apply rt_trans with a'; auto.
  apply rt_step; auto.

  eapply nec_ext_commut in H1 as [? ? ?]; eauto.
  eapply H0; eauto.
  etransitivity; eauto.
Qed.
Program Definition orp  (P Q:pred) : pred :=
   fun a:A => P a \/ Q a.
Next Obligation.
  left; eapply pred_hereditary; eauto.
  right; eapply pred_hereditary; eauto.
  left; eapply pred_upclosed; eauto.
  right; eapply pred_upclosed; eauto.
Qed.

Program Definition andp  (P Q:pred) : pred :=
   fun a:A => P a /\ Q a.

(* Universal and exp quantification
 *)

Program Definition allp  {B: Type} (f: B -> pred) : pred
  := fun a => forall b, f b a.
Next Obligation.
  apply pred_hereditary with a; auto.
  apply H0.

  apply pred_upclosed with a; auto.
  apply H0.
Qed.

Program Definition exp  {B: Type} (f: B -> pred) : pred
  := fun a => exists b, f b a.
Next Obligation.
  destruct H0; exists x; eapply pred_hereditary; eauto.

  destruct H0; exists x; eapply pred_upclosed; eauto.
Qed.


(* Definition of the "box" modal operator.  This operator turns
   modalities (relations) into a "necessarily" type operator.
 *)

Program Definition box  (M:modality) (P:pred) : pred :=
  fun a:A => forall a', M a a' -> P a'.
Next Obligation.
  destruct M as [M [? [H4 ?]]]; simpl in *.
  destruct (H4 _ _ H1 _ H).
  apply pred_hereditary with x; auto.
  apply H0; auto.

  destruct M as [M [? [? (*[*)H4 (*?]*)]]]; simpl in *.
  destruct (H4 _ _ H1 _ H).
  apply pred_upclosed with x; auto.
  apply H0; auto.
Qed.

(* Definition of the "diamond" modal operator.  This operator
   turns modalities into a "possibly" type operator.  _However_,
   note that this is NOT the boolean dual to "box", as usually
   found in accounts of modal logic. Instead, this is the
   "proof-theoretic" dual as found in Restall's "A Introduction
   to Substructural Logic" (2000).
 *)

(*Program Definition diamond  (M:modality) (P:pred) : pred :=
  fun a:A => exists a', M a' a /\ P a'.
Next Obligation.
  destruct M as [M [H3 ?]]; simpl in *.
  destruct H0 as [x [? ?]].
  destruct (H3 _ _ H _ H0).
  exists x0; split; auto.
  apply pred_hereditary with x; auto.

  destruct M as [M [? [? (*[*)? (*H3]*)]]]; simpl in *.
  destruct H0 as [x [? ?]].
  destruct (H3 _ _ H _ H0).
  exists x0; split; auto.
  apply pred_upclosed with x; auto.
Qed.*)

Definition boxy  (m: modality) (p: pred): Prop :=  box m p = p.

(* A pile of notations for the operators we have defined *)
Declare Scope pred_derives.
Notation "P '|--' Q" := (derives P%pred Q%pred) (at level 80, no associativity) : pred_derives.
Open Scope pred_derives.
Notation "'EX' x .. y , P " :=
  (exp (fun x => .. (exp (fun y => P%pred)) ..)) (at level 65, x binder, y binder, right associativity) : pred.
Notation "'ALL' x .. y , P " :=
  (allp (fun x => .. (allp (fun y => P%pred)) ..)) (at level 65, x binder, y binder, right associativity) : pred.
Infix "||" := orp (at level 50, left associativity) : pred.
Infix "&&" := andp (at level 40, left associativity) : pred.
Notation "P '-->' Q" := (imp P Q) (at level 55, right associativity) : pred.
Notation "P '<-->' Q" := (andp (imp P Q) (imp Q P)) (at level 57, no associativity) : pred.
(* Notation "'[]' e" := (box necM e) (at level 30, right associativity): pred. *)
Notation "'|>' e" := (box laterM e) (at level 20, right associativity): pred.
Notation "'!!' e" := (prop e) (at level 15) : pred.

(* Rules for the propositional connectives *)
Lemma modus_ponens  : forall (X P Q:pred),
  (X |-- P) ->
  (X |-- (P --> Q)) ->
  X |-- Q.
Proof.
  unfold derives, imp; simpl; intros.
  eapply H0 in H1; eauto.
Qed.

Lemma andp_right  : forall (X P Q:pred),
  (X |-- P) ->
  (X |-- Q) ->
  X |-- P && Q.
Proof.
  unfold derives, imp, andp; simpl; intuition.
Qed.


Lemma pred_ext' : forall (p1 p2:pred),
  app_pred p1 = app_pred p2 ->
  p1 = p2.
Proof.
  intros; destruct p1; destruct p2; simpl in H.
  subst x0.
  replace a0 with a by apply proof_irr.
  auto.
Qed.

Lemma pred_ext : forall (P Q:pred),
  derives P Q -> derives Q P -> P = Q.
Proof.
  intros.
  destruct P as [P HP].
  destruct Q as [Q HQ].
  unfold derives in *. simpl in *.
  apply (exist_ext (A->Prop) (fun p => hereditary (@age _ AG) p /\ hereditary (@ext_order _ AG EO) p)).
  extensionality a.
  apply prop_ext; intuition.
Qed.

Lemma andp_dup : forall P: pred, P && P = P.
Proof. intros. apply pred_ext; intros w ?. destruct H; auto. split; auto.
Qed.

Lemma andp_left1: forall P Q R: pred,  (P |-- R) -> P && Q |-- R.
Proof. repeat intro. destruct H0; auto.
Qed.

Lemma andp_left2: forall P Q R: pred,  (Q |-- R) -> P && Q |-- R.
Proof. repeat intro. destruct H0; auto.
Qed.

Lemma orp_left: forall P Q R: pred,  (P |-- R) -> (Q |-- R) -> P || Q |-- R.
Proof. repeat intro. destruct H1; auto.
Qed.

Lemma orp_right1: forall P Q R: pred,  (P |-- Q) -> P |-- Q || R.
Proof. repeat intro. left; auto.
Qed.

Lemma orp_right2: forall P Q R: pred,  (P |-- R) -> P |-- Q || R.
Proof. repeat intro. right; auto.
Qed.

Lemma orp_assoc  : forall P Q R: pred, (P || Q) || R = P || (Q || R).
Proof.
  intros; apply pred_ext; auto; unfold derives, andp; simpl; intuition.
Qed.

Lemma derives_trans :
    forall P Q R: pred, (P |-- Q) -> (Q |-- R) -> P |-- R.
Proof. firstorder. Qed.

Lemma exp_right:
  forall {B}(x:B) p (q: B -> pred),
    (p |-- q x) ->
    p |-- exp q.
Proof.
intros.
eapply derives_trans; try apply H.
intros w ?; exists x; auto.
Qed.

Lemma exp_left:
  forall {B: Type}(p: B -> pred) q,
  (forall x, p x |-- q) ->
   exp p |-- q.
Proof.
intros.
intros w [x' ?].
eapply H; eauto.
Qed.

Lemma and1  : forall (X P Q:pred),
  X |-- P && Q --> P.
Proof.
  unfold derives, imp, andp; simpl; intuition eauto.
Qed.

Lemma and2  : forall (X P Q:pred),
  X |-- P && Q --> Q.
Proof.
  unfold derives, imp, andp; simpl; intuition eauto.
Qed.

Lemma and3  : forall (X P Q R:pred),
  X |-- (P --> Q) --> (P --> R) --> (P --> Q && R).
Proof.
  unfold derives, imp, andp; simpl; intuition eauto.
  eapply nec_ext_commut in H4 as [? ? ?]; [|eauto].
  eapply H2.
  - eapply rt_trans; eauto.
  - etransitivity; eauto.
  - auto.
Qed.

Lemma or1  : forall (X P Q:pred),
  X |-- P --> P || Q.
Proof.
  unfold derives, imp, orp; simpl; intuition.
Qed.

Lemma or2  : forall (X P Q:pred),
  X |-- Q --> P || Q.
Proof.
  unfold derives, imp, orp; simpl; intuition.
Qed.

Lemma or3  : forall (X P Q R:pred),
  X |-- (P --> R) --> (Q --> R) --> (P || Q --> R).
Proof.
  unfold derives, imp, orp; simpl; intuition eauto.
  eapply nec_ext_commut in H4 as [? ? ?]; [|eauto].
  eapply H2.
  - eapply rt_trans; eauto.
  - etransitivity; eauto.
  - auto.
Qed.

Lemma TTrule  : forall X P,
  X |-- P --> TT.
Proof.
  unfold derives, imp, TT; simpl; intuition.
Qed.

Lemma FFrule  : forall X P,
  X |-- FF --> P.
Proof.
  unfold derives, imp, FF; simpl; intuition.
Qed.

Lemma distribution  : forall (X P Q R:pred),
  X |-- P && (Q || R) --> (P && Q) || (P && R).
Proof.
  unfold derives, imp, orp, andp; simpl; intuition.
Qed.

(* Characterize the relation between conjunction and implication *)
Lemma imp_andp_adjoint  : forall (P Q R:pred),
  ((P && Q) |-- R) <-> (P |-- (Q --> R)).
Proof.
  split; intros.
  hnf; intros; simpl; intros.
  apply H.
  split; auto.
  eapply pred_nec_hereditary, pred_upclosed in H0; eauto.
  hnf; intros.
  hnf in H.
  unfold imp in H; simpl in H.
  destruct H0.
  eapply H; eauto.
Qed.

(* Some facts about modalities *)

Lemma box_e0 : forall (M: modality) Q,
            reflexive _ M -> box M Q  |-- Q.
Proof.
intros.
intro; intros.
apply H0; simpl.
apply H.
Qed.

Lemma boxy_i :
  forall (Q: pred) (M: modality),
    reflexive _ M ->
    (forall w w', M w w' -> Q w -> Q w') ->
    boxy M Q.
Proof.
intros.
unfold boxy.
apply pred_ext; hnf; intros.
eapply box_e0; eauto.
hnf; intros.
eapply H0; eauto.
Qed.

(*
Lemma necM_refl : reflexive _ necM.
Proof.
intros; intro; simpl.
unfold necR.
constructor 2.
Qed.

#[export] Hint Resolve necM_refl.
*)

(* relationship between box and diamond *)
(*Lemma box_diamond  : forall M (P Q:pred),
  ((diamond M P) |-- Q) <-> (P |-- (box M Q)).
Proof.
  unfold derives; intuition.
  hnf; intros.
  apply H.
  hnf; eauto.
  destruct H0 as [a' [? ?]].
  apply H with a'; auto.
Qed.

(* Box is a normal modal operator *)

Lemma ruleNec  : forall M (P:pred),
  derives TT P ->
  derives TT (box M P).
Proof.
  intros.
  rewrite <- box_diamond.
  hnf; intros.
  apply H; hnf; auto.
Qed.*)

Lemma axiomK : forall M (P Q:pred),
  (box M (P --> Q)) |-- (box M P --> box M Q).
Proof.
  intros; do 3 (hnf; intros).
  destruct M as [R HR]; simpl in *.
  destruct (valid_rel_commut_ext2 R HR _ _ H3 _ H1) as [? ? HR'].
  destruct (valid_rel_commut_nec2 R HR _ _ HR' _ H0).
  eauto.
Qed.

(* Box and diamond are positive modal operators *)

Lemma box_positive  : forall M (P Q:pred),
  (P |-- Q) ->
  box M P |-- box M Q.
Proof.
  unfold derives, box; simpl; intuition.
Qed.

(*Lemma diamond_positive  : forall M (P Q:pred),
  (P |-- Q) ->
  diamond M P |-- diamond M Q.
Proof.
  unfold derives, diamond; simpl; firstorder.
Qed.*)

Lemma box_refl_trans : forall (m:modality) p,
  reflexive _ m ->
  transitive _ m ->
  box m (box m p) = box m p.
Proof.
  intros.
  apply pred_ext.
  repeat intro.
  assert (box m p a').
  apply H1; auto.
  apply H3.
  apply H.
  repeat intro.
  apply H1.
  eapply H0; eauto.
Qed.

(* Disribuitivity of box over various connectives *)

Lemma box_and : forall R (P Q:pred),
  box R (P && Q) = box R P && box R Q.
Proof.
  intros; apply pred_ext; hnf; intuition;
    unfold andp, box in *; simpl in *; firstorder.
Qed.

Lemma box_all  : forall B R (F:B -> pred),
  box R (allp F) = ALL x:B, box R (F x).
Proof.
  intros; apply pred_ext; hnf; intuition;
    unfold allp, box in *; simpl in *; firstorder.
Qed.

Lemma box_ex  : forall B R (F:B->pred),
  EX x:B, box R (F x) |-- box R (exp F).
Proof.
  unfold derives, exp, box; simpl; firstorder.
Qed.

Lemma box_or  : forall R (P Q:pred),
   box R P || box R Q |-- box R (P || Q).
Proof.
  unfold derives, orp, box; simpl; firstorder.
Qed.

(* Distributivity of diamond over various operators *)

(*Lemma diamond_or  : forall R (P Q:pred),
  diamond R (P || Q) = diamond R P || diamond R Q.
Proof.
  intros; apply pred_ext; hnf; intuition;
    unfold diamond, orp in *; simpl in *; firstorder.
Qed.

Lemma diamond_ex  : forall B R (F:B -> pred),
  diamond R (exp F) = EX x:B, diamond R (F x).
Proof.
  intros; apply pred_ext; hnf; intuition;
    unfold diamond, exp in *; simpl in *; firstorder.
Qed.

Lemma diamond_and  : forall R (P Q:pred),
  diamond R (P && Q) |-- diamond R P && diamond R Q.
Proof.
  unfold derives, andp, diamond; simpl; firstorder.
Qed.

Lemma diamond_all  : forall B R (F:B->pred),
  diamond R (allp F) |-- ALL x:B, diamond R (F x).
Proof.
  unfold derives, allp, diamond; simpl; firstorder.
Qed.*)


(* Lemmas about aging and the later operator *)

(*
Lemma nec_useless  :
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

Lemma later_age  : forall P,
  |>P = box ageM P.
Proof.
  intros; apply pred_ext; do 2 (hnf; intros).
  simpl in H.
  apply H.
  apply t_step; auto.
  revert H; induction H0; intros.
  apply H0; auto.
  apply pred_nec_hereditary with y.
  apply Rt_Rft; auto.
  apply IHclos_trans1; auto.
Qed.

Lemma now_later  : forall P,
  P |-- |>P.
Proof.
  repeat intro.
  apply pred_nec_hereditary with a; auto.
  apply Rt_Rft; auto.
Qed.

Lemma now_later2  : forall G P,
  (G |-- P) ->
  G |-- |>P.
Proof.
  intros; apply @derives_trans with P; auto.
  apply now_later.
Qed.

(* The "induction" rule for later *)

Lemma goedel_loeb  : forall (P Q:pred),
  (Q && |>P |-- P) ->
  Q |-- P.
Proof.
  intros; hnf; intro a.
  induction a using age_induction.
  intros; simpl in H.
  eapply H; auto.
  split; auto.
  rewrite later_age.
  simpl; intros.
  apply H0; auto.
  apply pred_hereditary with x; auto.
Qed.

Lemma loeb  : forall (P:pred),
     (|>P |-- P)    ->     TT |-- P.
Proof.
  intros. apply goedel_loeb.
  apply andp_left2. auto.
Qed.

(* Later distributes over almost everything! *)

(*Lemma later_commute_dia  : forall M (P:pred),
  diamond M (|> P) |-- |> (diamond M P).
Proof.
  intros.
  repeat rewrite later_age.
  do 3 (hnf; intros).
  simpl in H.
  firstorder.
  destruct M as [R HR].
  simpl in *.
  destruct HR as (H3 & _).
  destruct (H3 _ _ H0 _ H).
  exists x0; split; auto.
Qed.*)

Lemma later_commute  : forall M (P:pred),
  box M (|>P) = |>(box M P).
Proof.
  intros.
  apply pred_ext; do 3 (hnf; intros).
  destruct M as [R HR].
  destruct (valid_rel_commut_later2 R HR _ _ H1 _ H0).
  apply H with x; simpl; auto.
  destruct M as [R HR].
  destruct (valid_rel_commut_later1 R HR _ _ H1 _ H0).
  apply H with x; auto.
Qed.

Lemma later_and  : forall P Q,
  |>(P && Q) = |>P && |> Q.
Proof.
  intros; apply box_and.
Qed.

Lemma later_or  : forall (P Q:pred),
  |>(P || Q) = |>P || |>Q.
Proof.
  intros.
  repeat rewrite later_age.
  apply pred_ext.
  2: apply box_or.
  hnf; intros.
  simpl in H.
  case_eq (age1 a); intros.
  destruct (H a0); auto.
  left; simpl; intros.
  replace a' with a0; auto.
  congruence.
  right; simpl; intros.
  replace a' with a0; auto.
  congruence.
  left.
  hnf; simpl; intros.
  hnf in H1.
  rewrite H0 in H1; discriminate.
Qed.

Lemma later_ex  : forall B (F:B->pred),
  B ->
  |>(exp F) = EX x:B, |>(F x).
Proof.
  intros.
  apply pred_ext.
  2: apply box_ex.
  hnf; intros.
  rewrite later_age in H.
  case_eq (age1 a); intros.
  destruct (H a0); auto.
  exists x.
  rewrite later_age; simpl; intros.
  replace a' with a0; auto.
  congruence.
  exists X.
  rewrite later_age.
  hnf; simpl; intros.
  unfold age in H1.
  rewrite H0 in H1; discriminate.
Qed.

Lemma later_ex''  : forall B (F:B->pred),
  |>(exp F) |-- (EX x:B, |>(F x)) || |> FF.
Proof.
  intros.
  unfold derives; intros.
  simpl in H |- *.
  destruct (age1 a) eqn:?H; [left | right].
  + simpl in H.
    pose proof H a0.
    destruct H1 as [b ?].
    {
      constructor.
      auto.
    }
    exists b.
    intros.
    eapply pred_nec_hereditary, H1.
    eapply age_later_nec; eauto.
  + intros.
    clear - H1 H0.
    induction H1.
    - hnf in H; congruence.
    - auto.
Qed.

(*Lemma later_imp  : forall P Q,
  |>(P --> Q) = |>P --> |>Q.
Proof.
  intros; repeat rewrite later_age.
  apply pred_ext.
  apply axiomK.
  hnf; intros.
  simpl; intros.
  simpl in H.
  destruct valid_rel_nec as (_ & H4 & _).
  destruct (H4 _ _ H1 _ H0) as [? Hage ?].
  lapply (H x x).
  intros X.
  eapply ext_age_commut in Hage as []; eauto.
  eapply H; eauto.
  intros.
  replace a'1 with a''; auto.
  congruence.
Qed.*)

Lemma TT_boxy  : forall M,
  boxy M TT.
Proof.
  intros; hnf.
  apply pred_ext; repeat intro; simpl; auto.
Qed.

Lemma positive_boxy  : forall P Q M,
  boxy M P ->
  (P |-- Q) ->
  P |-- box M Q.
Proof.
  intros.
  rewrite <- H.
  apply box_positive.
  auto.
Qed.

Lemma forallI  : forall A G X,
  (forall x:A, G |-- X x) ->
  G |-- allp X.
Proof.
  repeat intro.
  eapply H; auto.
Qed.

Lemma TT_and  : forall P,
  TT && P = P.
Proof.
  intros; apply pred_ext; repeat intro.
  destruct H; auto.
  split; simpl; auto.
Qed.

Lemma andp_comm  : forall P Q,
  P && Q = Q && P.
Proof.
  intros; apply pred_ext; unfold andp; repeat intro; simpl in *; intuition.
Qed.

Lemma andp_assoc  : forall P Q R,
  (P && Q) && R = P && (Q && R).
Proof.
  intros; apply pred_ext; auto; unfold derives, andp; simpl; intuition.
Qed.

Lemma ex_and : forall  B (P:B->pred) Q,
  (exp P) && Q = EX x:B, P x && Q.
Proof.
  intros. apply pred_ext.
  repeat intro. destruct H. destruct H.
  exists x. split; auto.
  repeat intro.
  destruct H. destruct H.
  split; auto. exists x; auto.
Qed.

Lemma FF_and : forall  (P:pred),
  FF && P = FF.
Proof.
  intros. apply pred_ext; repeat intro.
  destruct H; auto.
  elim H.
Qed.


Lemma boxy_e : forall (M: modality) P,  boxy M P ->
           forall w w', app_mode M w w' -> P w -> P w'.
Proof.
intros.
rewrite <- H in H1; eauto.
Qed.

Lemma boxy_andp :
     forall (M: modality), reflexive _ (app_mode M) ->
      forall P Q, boxy M P -> boxy M Q -> boxy M (P && Q).
Proof.
destruct M;
intros.
simpl in *.
apply boxy_i; intros; auto.
destruct H3.
simpl.
split; eapply boxy_e; eauto.
Qed.

#[local] Hint Resolve boxy_andp : core.

Lemma boxy_disjunction :
     forall (M: modality) , reflexive _ (app_mode M) ->
      forall P Q, boxy M P -> boxy M Q -> boxy M (P || Q).
Proof.
destruct M;
intros.
simpl in *.
apply boxy_i; intros; auto.
destruct H3.
left.  eapply boxy_e; eauto.
right. eapply boxy_e; eauto.
Qed.

#[local] Hint Resolve boxy_disjunction : core.

Lemma boxy_exp :
    forall (M: modality) T (P: T -> pred),
     reflexive _ (app_mode M) ->
     (forall x, boxy M (P x)) -> boxy M (exp P).
Proof.
intros.
apply boxy_i; auto; intros.
destruct H2 as [x ?].
rewrite <- H0 in H2.
specialize ( H2 w' H1).
econstructor; eauto.
Qed.

#[local] Hint Resolve boxy_exp : core.

Lemma boxy_prop :  forall (M: modality) P, reflexive _ (app_mode M) -> boxy M (prop P).
Proof.
intros.
apply boxy_i; auto.
Qed.

Lemma boxy_TT :  forall (M: modality), reflexive _ (app_mode M) -> boxy M TT.
Proof.
intros.
apply boxy_i; intros; auto.
Qed.

Lemma boxy_FF :  forall (M: modality), reflexive _ (app_mode M) -> boxy M FF.
Proof.
intros; apply boxy_i; intros; auto; contradiction.
Qed.

#[local] Hint Resolve boxy_TT : core.
#[local] Hint Resolve boxy_FF : core.

Lemma TT_i  : forall w: A,  app_pred TT w.
Proof.
unfold TT, prop; simpl; auto.
Qed.

#[local] Hint Resolve TT_i : core.

Lemma prop_andp_left : forall (P: Prop) Q R, (P -> Q |-- R) -> !!P && Q |-- R.
Proof.
 repeat intro. destruct H0; auto. apply H; auto.
Qed.

Lemma prop_andp_right : forall (P: Prop) Q R, P -> (Q |-- R) -> Q |-- !!P && R.
Proof.
 repeat intro. split; auto.
Qed.

Lemma prop_true_andp:
  forall (P: Prop) (Q: pred), P -> (!! P && Q = Q).
Proof.
intros.
apply pred_ext.
unfold derives; intros ? [? ?]; auto.
unfold derives; intros; split; auto.
Qed.

Lemma prop_false_andp:
  forall (P: Prop) (Q: pred), ~P -> !! P && Q = FF.
Proof.
intros.
apply pred_ext.
unfold derives; intros ? [? ?]; tauto.
unfold derives. intros ? [].
Qed.

Lemma prop_andp_e :  forall P Q (w:A), (!! P && Q) w -> P /\ Q w.
Proof.
intuition; destruct H; auto.
Qed.

Lemma prop_andp_i :  forall P Q (w:A), P /\ app_pred Q w -> (!! P && Q) w.
Proof.
intuition.
split; auto.
Qed.

Lemma later_derives : forall {P Q}, (P |-- Q) -> (|> P |-- |> Q).
Proof.
unfold derives; intros.
intro; intros; eapply H.
eauto.
Qed.

Lemma boxy_allp :
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
specialize (H2 b).
rewrite <- H0 in H2.
apply H2; auto.
Qed.
#[local] Hint Resolve boxy_allp : core.

Lemma later_allp :
       forall B P, |> (allp P) = allp (fun x:B => |> (P x)).
Proof.
intros.
apply pred_ext; unfold derives; simpl; intros; eapply H; eauto.
Qed.

Lemma later_prop :
       forall P: Prop, |> (prop P) |-- prop P || |> FF.
Proof.
  intros.
  unfold derives; intros.
  simpl in H |- *.
  destruct (age1 a) eqn:?H; [left | right].
  + apply (H a0).
    unfold laterR.
    constructor.
    auto.
  + intros.
    clear - H0 H1.
    induction H1.
    - hnf in H; congruence.
    - auto.
Qed.

Lemma box_derives  : forall M (P Q:pred),
  (P |-- Q) ->  box M P |-- box M Q.
Proof. exact box_positive. Qed.

Lemma allp_derives:
       forall (B: Type) (P Q: B -> pred),
               (forall x:B, P x |-- Q x) -> (allp P |-- allp Q).
Proof.
intros.
intros w b ?.
eapply H; eauto.
Qed.

Lemma forall_pred_ext  : forall B (P Q: B -> pred),
 (ALL x : B, (P x <--> Q x)) |-- (ALL x : B, P x) <--> (ALL x: B, Q x) .
Proof.
intros.
intros w ?.
split; intros ? ? ? ? ? ?; destruct (H b); eauto.
Qed.

Lemma exists_pred_ext  : forall B (P Q: B -> pred),
 (ALL x : B, (P x <--> Q x)) |-- (EX x : B, P x) <--> (EX x: B, Q x) .
Proof.
intros.
intros w ?.
split; intros w' ? ? ? [? ?]; exists x; eapply H; eauto.
Qed.

Lemma imp_pred_ext  : forall B B' P Q,
       (B <--> B') && (B --> (P <--> Q))
 |-- (B --> P) <-->  (B' --> Q).
Proof.
intros.
intros w [? ?].
split; intros ? w'' ? Hext ? ? w3 Hnec' ? ?.
eapply nec_ext_commut in Hext as []; [|eauto].
eapply H0.
eapply rt_trans; eauto.
etransitivity; eauto.
eapply H.
eapply rt_trans; eauto.
etransitivity; eauto.
auto.
apply rt_refl.
reflexivity.
eapply H2; eauto.
eapply H.
eapply rt_trans; eauto.
etransitivity; eauto.
auto.
eapply nec_ext_commut in Hext as []; [|eauto].
eapply H0.
eapply rt_trans; eauto.
etransitivity; eauto.
eapply H.
eapply rt_trans; eauto.
etransitivity; eauto.
eapply H.
eapply rt_trans; eauto.
etransitivity; eauto.
auto.
apply rt_refl.
reflexivity.
eapply H2; eauto.
eapply H.
eapply rt_trans; eauto.
etransitivity; eauto.
auto.
Qed.

Lemma derives_refl:
  forall (P: pred), (P |-- P).
Proof. firstorder.
Qed.

#[local] Hint Resolve derives_refl : core.

Lemma andp_derives :
  forall P Q P' Q': pred, (P |-- P') -> (Q |-- Q') -> P && Q |-- P' && Q'.
Proof.
intros.
intros w [? ?]; split; auto.
Qed.

Lemma orp_derives :
  forall P Q P' Q': pred, (P |-- P') -> (Q |-- Q') -> P || Q |-- P' || Q'.
Proof.
intros.
 apply orp_left. apply orp_right1; auto. apply orp_right2; auto.
Qed.

Lemma exp_derives :
       forall B (P: B -> pred) Q , (forall x:B, P x |-- Q x) -> (exp P |-- exp Q).
Proof.
intros.
intros w [b ?].
exists b; eapply H; eauto.
Qed.

Lemma box_ext : forall (M: modality) P Q,
    box M (P <--> Q) |--  box M P <--> box M Q.
Proof.
intros.
repeat rewrite box_and.
apply andp_right;
eapply derives_trans; try apply axiomK; intros ? [? ?]; auto.
Qed.

Lemma andp_pred_ext : forall P Q P' Q',
       (P <--> P') && (Q <--> Q') |--  (P && Q) <--> (P' && Q').
Proof.
intros.
intros w [? ?].
split; (intros w' ? ? ? [? ?]; split; [eapply H; eauto | eapply H0; eauto]).
Qed.

Program Definition exactly  (x: A) : pred := fun w => exists y, necR x y /\ ext_order y w.
Next Obligation.
destruct H0 as (? & Hnec & Hext).
eapply age_ext_commut in Hext as [? Hext ?]; eauto.
do 2 eexists; [|apply Hext].
eapply rt_trans; eauto.
apply rt_step; auto.

destruct H0 as (? & Hnec & Hext).
do 2 eexists; eauto.
etransitivity; eauto.
Qed.

Lemma derives_TT : forall (P: pred), P |-- TT.
Proof.
intros.
intros ? ?; auto.
Qed.
#[local] Hint Resolve derives_TT : core.

Lemma FF_derives : forall P, FF |-- P.
Proof.
intros. intros ? ?. hnf in H; contradiction.
Qed.
#[local] Hint Immediate FF_derives : core.

Lemma necR_level' : forall {w w': A}, necR w w' ->
       @necR _ ag_nat (level w) (level w').
Proof.
induction 1; simpl; intros.
apply age_level in H. constructor 1.  unfold age, age1; simpl.  rewrite H; reflexivity.
constructor 2.
constructor 3 with (level y); auto.
Qed.

Lemma derives_imp :
  forall P Q w, (P |-- Q) -> (P --> Q) w.
Proof.
intros.
intros ????; auto.
Qed.

Lemma exp_andp1 :
 forall B (p: B -> pred) q, (exp p && q)%pred = (exp (fun x => p x && q))%pred.
Proof.
intros; apply pred_ext; intros w ?.
destruct H.
destruct H.
exists x; split; auto.
destruct H. destruct H.
split; auto.
exists x; auto.
Qed.

Lemma exp_andp2 :
 forall B p (q: B -> pred), (p && exp q)%pred = (exp (fun x => p && q x))%pred.
Proof.
intros; apply pred_ext; intros w ?.
destruct H.
destruct H0.
exists x; split; auto.
destruct H. destruct H.
split; auto.
exists x; auto.
Qed.

Lemma exp_imp_left :  forall B (p: B -> pred) q,
     (exp p --> q)%pred = allp (fun x => p x --> q)%pred.
Proof.
intros; apply pred_ext; intros w ?.
intro.
intros ? ?w ? ? ?.
eapply H; eauto.
exists b; auto.
intros ?w ? ? ? [? ?].
eapply H; eauto.
Qed.

Lemma app_ext  : forall (F G: A -> Prop) p1 p2 w,
         (F w = G w) ->
         app_pred (exist (fun P => hereditary age P /\ hereditary ext_order P) F p1) w = app_pred (exist (fun P => hereditary age P /\ hereditary ext_order P) G p2) w.
Proof.
simpl; auto.
Qed.

Lemma imp_derives :
  forall P P' Q Q',
    (P' |-- P) ->
    (Q |-- Q') ->
    P --> Q |-- P' --> Q'.
Proof.
intros.
intros w ? ? w'' ? ? ?.
apply H0.
eapply H1; eauto.
Qed.


Lemma imp_lem0  :  forall P st, (TT --> P) st -> P st.
Proof.
intros; eauto.
Qed.

Lemma conjoin_hyp0  :
      forall (P Q: pred) w,  P w -> (P --> Q) w -> (TT --> Q) w.
Proof.
intros.
intros w' ? ? ? ?.
eapply H0;
eauto.
eapply pred_nec_hereditary, pred_upclosed in H; eauto.
Qed.

Lemma conjoin_hyp1 : forall (P Q R: pred)  w,
            P w -> (P&&Q --> R) w -> (Q --> R) w.
Proof.
intros.
intros w' ? ? ? ?.
eapply H0; try eassumption.
split; eauto.
eapply pred_nec_hereditary, pred_upclosed in H; eauto.
Qed.

Lemma derives_e : forall p q (st: A),
      (p |-- q) -> p st -> q st.
Proof.
auto.
Qed.

Lemma later_andp :
  forall P Q, |> (P && Q) = |>P && |>Q.
Proof.
intros.
apply pred_ext; intros w ?.
split; intros w' ?; destruct (H _ H0); auto.
destruct H.
intros w' ?; split; eauto.
Qed.

Lemma True_andp_eq :
  forall (P: Prop) (Q: pred), P -> (!!P && Q)%pred = Q.
intros.
apply pred_ext; intros w ?; hnf in *; simpl; intros; intuition.
Qed.

Lemma distrib_orp_andp :
   forall P Q R, (P||Q)&&R = (P&&R)||(Q&&R).
Proof.
  intros. apply pred_ext.
  intros w [[?|?] ?]; [left|right]; split; auto.
  intros w [[? ?]|[? ?]]; split; auto. left; auto. right; auto.
Qed.

Lemma allp_right {B: Type}:
  forall (P: pred) (Q: B -> pred),
  (forall v, P |-- Q v) ->
   P |-- allp Q.
Proof.
 intros. intros w ? v; apply (H v); auto.
Qed.

Lemma allp_left {B}:
   forall (P: B -> pred) x Q, (P x |-- Q) -> allp P |-- Q.
 Proof.
   intros. intros ? ?. apply H. apply H0.
Qed.

(*Lemma later_imp2 : forall P Q: pred,
                 |> (P <--> Q) = |> P <--> |> Q.
Proof.
 intros.
  repeat rewrite <- later_imp. rewrite <- later_andp; auto.
Qed.*)

End Order.

Arguments pred A {AG EO}.

#[export] Hint Resolve pred_hereditary : core.
#[export] Hint Resolve rt_refl rt_trans t_trans : core.
#[export] Hint Unfold necR : core.
#[export] Hint Resolve boxy_andp : core.
#[export] Hint Resolve boxy_disjunction : core.
#[export] Hint Resolve boxy_exp : core.
#[export] Hint Resolve boxy_TT : core.
#[export] Hint Resolve boxy_FF : core.
#[export] Hint Resolve TT_i : core.
#[export] Hint Resolve boxy_allp : core.
#[export] Hint Resolve derives_refl : core.
#[export] Hint Resolve derives_TT : core.
#[export] Hint Immediate FF_derives : core.

Declare Scope pred_derives.
Notation "P '|--' Q" := (derives P%pred Q%pred) (at level 80, no associativity) : pred_derives.
Open Scope pred_derives.
Notation "'EX' x .. y , P " :=
  (exp (fun x => .. (exp (fun y => P%pred)) ..)) (at level 65, x binder, y binder, right associativity) : pred.
Notation "'ALL' x .. y , P " :=
  (allp (fun x => .. (allp (fun y => P%pred)) ..)) (at level 65, x binder, y binder, right associativity) : pred.
Infix "||" := orp (at level 50, left associativity) : pred.
Infix "&&" := andp (at level 40, left associativity) : pred.
Notation "P '-->' Q" := (imp P Q) (at level 55, right associativity) : pred.
Notation "P '<-->' Q" := (andp (imp P Q) (imp Q P)) (at level 57, no associativity) : pred.
(* Notation "'[]' e" := (box necM e) (at level 30, right associativity): pred. *)
Notation "'|>' e" := (box laterM e) (at level 20, right associativity): pred.
Notation "'!!' e" := (prop e) (at level 15) : pred.

Ltac slurp :=
 apply imp_lem0;
  match goal with |-  app_pred (_ --> _)  ?st =>
        repeat match goal with
                   | H: app_pred ?P st |- app_pred (?b --> ?c) st =>
                       (apply (@conjoin_hyp0 _ _ _ P c st H) ||
                        (apply (@conjoin_hyp1 _ _ _ P b c st H)));
                       clear H
                   end;
        try (revert st; apply derives_e)
  end.

Lemma test_slurp {A} {agA : ageable A} {EO : Ext_ord A} :  forall (P Q R S : pred A) w ,
        (P && (Q && R) --> S) w -> P w -> Q w -> R w -> S w.
Proof.
intros.
remember (app_pred (P && (Q && R) --> S) w) as hide.
slurp.
subst hide. assumption.
Qed.
