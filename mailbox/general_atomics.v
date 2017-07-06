Require Import veric.rmaps.
Require Import veric.compcert_rmaps.
Require Import progs.conclib.
Require Import progs.ghost.
Require Import floyd.library.
Require Import floyd.sublist.

Set Bullet Behavior "Strict Subproofs".

Parameter invariant : mpred -> mpred.

Axiom invariant_precise : forall P, precise (invariant P).

(* In Iris, invariants are named and impredicative, and so the rules are full of laters. If we forgo
   impredicative invariants, we can drop the laters. The contents of an invariant can still be impredicative
   using HORec or the like. *)

(* I think this is sound, and follows from Iris's rules... *)
Axiom invariant_view_shift : forall {CS : compspecs} P Q R, view_shift (P * R) (Q * R) ->
  view_shift (P * invariant R) (Q * invariant R).

Lemma invariants_view_shift : forall {CS : compspecs} lR P Q,
  view_shift (P * fold_right sepcon emp lR) (Q * fold_right sepcon emp lR) ->
  view_shift (P * fold_right sepcon emp (map invariant lR)) (Q * fold_right sepcon emp (map invariant lR)).
Proof.
  induction lR; auto; simpl; intros.
  rewrite <- !sepcon_assoc; apply IHlR.
  rewrite !sepcon_assoc, !(sepcon_comm (invariant _)), <- !sepcon_assoc.
  apply invariant_view_shift.
  etransitivity; [|etransitivity; eauto]; apply derives_view_shift; cancel.
Qed.

Axiom invariant_super_non_expansive : forall n P, approx n (invariant P) =
approx n (invariant (approx n P)).

Global Arguments view_shift {_} A%logic B%logic.

Section atomics.

Context {CS : compspecs}.

(* To avoid carrying views with protocol assertions, we instead forbid them from appearing in invariants. *)
Parameter objective : mpred -> Prop.
Axiom emp_objective : objective emp.
Axiom data_at_objective : forall sh t v p, readable_share sh -> objective (data_at sh t v p).
Axiom ghost_objective : forall {A} {P : PCM A} (g : A) p, objective (ghost g p).
Axiom prop_objective : forall P, objective (!!P).
Axiom andp_objective : forall P Q, objective P -> objective Q -> objective (P && Q).
Axiom exp_objective : forall {A} P, (forall x, objective (P x)) -> objective (EX x : A, P x).
Axiom sepcon_objective : forall P Q, objective P -> objective Q -> objective (P * Q).
Lemma sepcon_list_objective : forall P, Forall objective P -> objective (fold_right sepcon emp P).
Proof.
  induction P; simpl; intros.
  - apply emp_objective.
  - inv H; apply sepcon_objective; auto.
Qed.

Axiom new_inv : forall P, objective P -> view_shift P (invariant P).

Corollary make_inv : forall P Q, P |-- Q -> objective Q -> view_shift P (invariant Q).
Proof.
  intros.
  etransitivity; [apply derives_view_shift | apply new_inv]; auto.
Qed.

Section dup.

Definition duplicable P := view_shift P (P * P).

Lemma emp_duplicable : duplicable emp.
Proof.
  repeat intro.
  rewrite sepcon_emp in H; auto.
Qed.
Hint Resolve emp_duplicable : dup.

Lemma sepcon_duplicable : forall P Q, duplicable P -> duplicable Q -> duplicable (P * Q).
Proof.
  intros; unfold duplicable.
  rewrite <- sepcon_assoc, (sepcon_comm (_ * Q)), <- sepcon_assoc, sepcon_assoc.
  apply view_shift_sepcon; auto.
Qed.
Hint Resolve sepcon_duplicable : dup.

Lemma sepcon_list_duplicable : forall lP, Forall duplicable lP -> duplicable (fold_right sepcon emp lP).
Proof.
  induction 1; simpl; auto with dup.
Qed.

Lemma list_duplicate : forall Q lP, duplicable Q ->
  view_shift (fold_right sepcon emp lP * Q) (fold_right sepcon emp (map (sepcon Q) lP) * Q).
Proof.
  induction lP; simpl; intros; [reflexivity|].
  rewrite sepcon_assoc; etransitivity; [apply view_shift_sepcon2, IHlP; auto|].
  rewrite <- sepcon_assoc; etransitivity; [apply view_shift_sepcon2, H|].
  apply derives_view_shift; cancel.
Qed.

(* Should all duplicables be of this form? *)
Axiom invariant_duplicable : forall P, invariant P = invariant P * invariant P.

Lemma invariant_duplicable' : forall P, duplicable (invariant P).
Proof.
  repeat intro; rewrite <- invariant_duplicable in *; auto.
Qed.
Hint Resolve invariant_duplicable' : dup.

Lemma ghost_snap_duplicable : forall `{_ : PCM_order} (s : A) p, duplicable (ghost_snap s p).
Proof.
  intros; unfold duplicable.
  erewrite ghost_snap_join; [reflexivity|].
  apply ord_join; reflexivity.
Qed.
Hint Resolve ghost_snap_duplicable : dup.

Lemma prop_duplicable : forall P Q, duplicable Q -> duplicable (!!P && Q).
Proof.
  intros.
  apply view_shift_prop; intro.
  etransitivity; eauto.
  apply derives_view_shift; entailer!.
Qed.
Hint Resolve prop_duplicable : dup.

Lemma exp_duplicable : forall {A} (P : A -> mpred), (forall x, duplicable (P x)) -> duplicable (exp P).
Proof.
  unfold duplicable; intros.
  view_shift_intro x.
  etransitivity; eauto.
  apply derives_view_shift; Exists x x; auto.
Qed.

Lemma duplicable_super_non_expansive : forall n P,
  approx n (!!duplicable P) = approx n (!!duplicable (approx n P)).
Proof.
  intros; unfold duplicable.
  setoid_rewrite view_shift_super_non_expansive at 1; rewrite approx_sepcon; auto.
Qed.

End dup.

Definition AL_type := ProdType (ProdType (ProdType (ProdType (ProdType (ConstType val) Mpred)
  (ArrowType (ConstType Z) Mpred)) (ConstType (list Z)))
  (ArrowType (ConstType share) (ArrowType (ConstType Z) Mpred))) (ArrowType (ConstType Z) Mpred).

(* For this to work with load_acquire, Q needs to be somehow future-proof: it should be okay even if v wasn't
   actually the latest value of tgt. Only getting knowledge isn't enough: P' v must be something that still
   holds even if the actual value at p has been changed from v. *)
(* GPS's protocols are equivalent to saying that P' can only place one-sided bounds on the values of atomic
   memory locations, rather than giving ownership of them or precisely constraining them. GPS does part of this
   by insisting that Q = P * Q', where Q' is persistent. The rest follows from the fact that atomic locations
   can *only* be the subject of protocol assertions. *)
Program Definition load_SC_spec := TYPE AL_type
  WITH p : val, P : mpred, II : Z -> mpred, lI : list Z, P' : share -> Z -> mpred, Q : Z -> mpred
  PRE [ 1%positive OF tptr tint ]
   PROP (view_shift (fold_right sepcon emp (map II lI) * P)
           (EX sh : share, EX v : Z, !!(readable_share sh /\ repable_signed v) &&
              data_at sh tint (vint v) p * P' sh v);
         forall sh v, view_shift (!!(readable_share sh /\ repable_signed v) &&
           data_at sh tint (vint v) p * P' sh v) (fold_right sepcon emp (map II lI) * Q v))
   LOCAL (temp 1%positive p)
   SEP (fold_right sepcon emp (map (fun p => invariant (II p)) lI); P)
  POST [ tint ]
   EX v : Z,
   PROP (repable_signed v)
   LOCAL (temp ret_temp (vint v))
   SEP (fold_right sepcon emp (map (fun p => invariant (II p)) lI); Q v).
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((((?, ?), ?), ?), ?), ?); simpl.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal; [rewrite ?prop_and, ?approx_andp |
    f_equal; rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem].
  - f_equal; [|f_equal].
    + rewrite view_shift_super_non_expansive.
      setoid_rewrite view_shift_super_non_expansive at 2; do 2 apply f_equal; f_equal.
      * rewrite !approx_sepcon, !approx_sepcon_list', approx_idem.
        erewrite !map_map, map_ext; eauto.
        intro; simpl; rewrite approx_idem; auto.
      * rewrite !approx_exp; apply f_equal; extensionality sh.
        rewrite !approx_exp; apply f_equal; extensionality v.
        rewrite !approx_sepcon, approx_idem; auto.
    + rewrite !prop_forall, !(approx_allp _ _ _ Share.bot); apply f_equal; extensionality sh.
      rewrite !prop_forall, !(approx_allp _ _ _ 0); apply f_equal; extensionality v.
      rewrite view_shift_super_non_expansive.
      setoid_rewrite view_shift_super_non_expansive at 2; do 2 apply f_equal; f_equal.
      * rewrite !approx_sepcon, approx_idem; auto.
      * rewrite !approx_sepcon, !approx_sepcon_list', approx_idem.
        erewrite !map_map, map_ext; eauto.
        intro; simpl; rewrite approx_idem; auto.
  - rewrite !approx_sepcon_list'.
    erewrite !map_map, map_ext; eauto.
    intros; simpl; rewrite invariant_super_non_expansive; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((((?, ?), ?), ?), ?), ?); simpl.
  rewrite !approx_exp; apply f_equal; extensionality v.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem.
  rewrite !approx_sepcon_list'.
  erewrite !map_map, map_ext; eauto.
  intros; simpl; rewrite invariant_super_non_expansive; auto.
Qed.

Definition AS_type := ProdType (ProdType (ProdType (ProdType (ProdType (ConstType (val * Z)) Mpred)
  (ArrowType (ConstType Z) Mpred)) (ConstType (list Z))) (ArrowType (ConstType share) Mpred)) Mpred.

Program Definition store_SC_spec := TYPE AS_type
  WITH p : val, v : Z, P : mpred, II : Z -> mpred, lI : list Z, P' : share -> mpred, Q : mpred
  PRE [ 1%positive OF tptr tint, 2%positive OF tint ]
   PROP (repable_signed v;
         view_shift (fold_right sepcon emp (map II lI) * P)
           (EX sh : share, !!(writable_share sh) && data_at_ sh tint p * P' sh);
         forall sh, view_shift (!!(writable_share sh) && data_at sh tint (vint v) p * P' sh)
           (fold_right sepcon emp (map II lI) * Q))
   LOCAL (temp 1%positive p; temp 2%positive (vint v))
   SEP (fold_right sepcon emp (map (fun p => invariant (II p)) lI); P)
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (fold_right sepcon emp (map (fun p => invariant (II p)) lI); Q).
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((((?, ?), ?), ?), ?), ?), ?); simpl.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal; [rewrite ?prop_and, ?approx_andp |
    f_equal; rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem].
  - apply f_equal; f_equal; [|f_equal].
    + rewrite view_shift_super_non_expansive.
      setoid_rewrite view_shift_super_non_expansive at 2; do 2 apply f_equal; f_equal.
      * rewrite !approx_sepcon, !approx_sepcon_list', approx_idem.
        erewrite !map_map, map_ext; eauto.
        intro; simpl; rewrite approx_idem; auto.
      * rewrite !approx_exp; apply f_equal; extensionality sh.
        rewrite !approx_sepcon, approx_idem; auto.
    + rewrite !prop_forall, !(approx_allp _ _ _ Share.bot); apply f_equal; extensionality sh.
      rewrite view_shift_super_non_expansive.
      setoid_rewrite view_shift_super_non_expansive at 2; do 2 apply f_equal; f_equal.
      * rewrite !approx_sepcon, approx_idem; auto.
      * rewrite !approx_sepcon, !approx_sepcon_list', approx_idem.
        erewrite !map_map, map_ext; eauto.
        intro; simpl; rewrite approx_idem; auto.
  - rewrite !approx_sepcon_list'.
    erewrite !map_map, map_ext; eauto.
    intros; simpl; rewrite invariant_super_non_expansive; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((((?, ?), ?), ?), ?), ?), ?); simpl.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem.
  rewrite !approx_sepcon_list'.
  erewrite !map_map, map_ext; eauto.
  intros; simpl; rewrite invariant_super_non_expansive; auto.
Qed.

Definition ACAS_type := ProdType (ProdType (ProdType (ProdType (ProdType (ConstType (val * Z * Z)) Mpred)
  (ArrowType (ConstType Z) Mpred)) (ConstType (list Z)))
  (ArrowType (ConstType share) (ArrowType (ConstType Z) Mpred))) (ArrowType (ConstType Z) Mpred).

Program Definition CAS_SC_spec := TYPE ACAS_type
  WITH p : val, c : Z, v : Z, P : mpred, II : Z -> mpred, lI : list Z, P' : share -> Z -> mpred,
       Q : Z -> mpred
  PRE [ 1%positive OF tptr tint, 2%positive OF tint, 3%positive OF tint ]
   PROP (repable_signed c; repable_signed v;
         view_shift (fold_right sepcon emp (map II lI) * P)
           (EX sh : share, EX v0 : Z, !!(writable_share sh /\ repable_signed v0) &&
              data_at sh tint (vint v0) p * P' sh v0);
         forall sh v0, view_shift (!!(writable_share sh /\ repable_signed v0) &&
           data_at sh tint (vint (if eq_dec v0 c then v else v0)) p * P' sh v0)
           (fold_right sepcon emp (map II lI) * Q v0))
   LOCAL (temp 1%positive p; temp 2%positive (vint c); temp 3%positive (vint v))
   SEP (fold_right sepcon emp (map (fun p => invariant (II p)) lI); P)
  POST [ tint ]
   EX v' : Z,
   PROP (repable_signed v')
   LOCAL (temp ret_temp (vint (if eq_dec v' c then 1 else 0)))
   SEP (fold_right sepcon emp (map (fun p => invariant (II p)) lI); Q v').
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((((((?, ?), ?), ?), ?), ?), ?), ?); simpl.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal; [rewrite ?prop_and, ?approx_andp |
    f_equal; rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem].
  - do 2 apply f_equal; f_equal; [|f_equal].
    + rewrite view_shift_super_non_expansive.
      setoid_rewrite view_shift_super_non_expansive at 2; do 2 apply f_equal; f_equal.
      * rewrite !approx_sepcon, !approx_sepcon_list', approx_idem.
        erewrite !map_map, map_ext; eauto.
        intro; simpl; rewrite approx_idem; auto.
      * rewrite !approx_exp; apply f_equal; extensionality sh.
        rewrite !approx_exp; apply f_equal; extensionality v0.
        rewrite !approx_sepcon, approx_idem; auto.
    + rewrite !prop_forall, !(approx_allp _ _ _ Share.bot); apply f_equal; extensionality sh.
      rewrite !prop_forall, !(approx_allp _ _ _ 0); apply f_equal; extensionality v0.
      rewrite view_shift_super_non_expansive.
      setoid_rewrite view_shift_super_non_expansive at 2; do 2 apply f_equal; f_equal.
      * rewrite !approx_sepcon, approx_idem; auto.
      * rewrite !approx_sepcon, !approx_sepcon_list', approx_idem.
        erewrite !map_map, map_ext; eauto.
        intro; simpl; rewrite approx_idem; auto.
  - rewrite !approx_sepcon_list'.
    erewrite !map_map, map_ext; eauto.
    intros; simpl; rewrite invariant_super_non_expansive; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((((((?, ?), ?), ?), ?), ?), ?), ?); simpl.
  rewrite !approx_exp; apply f_equal; extensionality vr.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem.
  rewrite !approx_sepcon_list'.
  erewrite !map_map, map_ext; eauto.
  intros; simpl; rewrite invariant_super_non_expansive; auto.
Qed.

Section atomicity.

(* The logical atomicity of Iris, with TaDa's private part. *)
Definition view_shift_iff P Q := view_shift P Q /\ view_shift Q P.

Definition atomic_shift {A B} P (a R : A -> mpred) E (b Q : A -> B -> mpred) :=
  view_shift_iff (fold_right sepcon emp E * P) (EX x : A, a x * R x) /\
  forall x v, view_shift (b x v * R x) (fold_right sepcon emp E * Q x v).

Definition atomic_spec_type A W T := ProdType (ProdType (ProdType (ProdType (ProdType W Mpred)
  ((ArrowType (ConstType A) (ArrowType (ConstType T) Mpred)))) (ArrowType (ConstType A) Mpred))
  (ArrowType (ConstType Z) Mpred)) (ConstType (list Z)).

Definition super_non_expansive_a {A W} (a : forall ts : list Type, functors.MixVariantFunctor._functor
  (dependent_type_functor_rec ts W) (predicates_hered.pred rmap) -> A -> predicates_hered.pred rmap) :=
  forall n ts w x, approx n (a ts w x) =
  approx n (a ts (functors.MixVariantFunctor.fmap (dependent_type_functor_rec ts W) (approx n) (approx n) w) x).

Definition super_non_expansive_b {A B W} (b : forall ts : list Type, functors.MixVariantFunctor._functor
  (dependent_type_functor_rec ts W) (predicates_hered.pred rmap) -> A -> B -> predicates_hered.pred rmap) :=
  forall n ts w x y, approx n (b ts w x y) =
  approx n (b ts (functors.MixVariantFunctor.fmap (dependent_type_functor_rec ts W) (approx n) (approx n) w) x y).

Definition super_non_expansive_la {W} la := forall n ts w rho,
  Forall (fun l => approx n (!! locald_denote (l ts w) rho) = approx n (!! locald_denote (l ts
    (functors.MixVariantFunctor.fmap (dependent_type_functor_rec ts W) (approx n) (approx n) w)) rho)) la.

Definition super_non_expansive_lb {B W} lb := forall n ts w (v : B) rho,
  Forall (fun l => approx n (!! locald_denote (l ts w v) rho) = approx n (!! locald_denote (l ts
    (functors.MixVariantFunctor.fmap (dependent_type_functor_rec ts W) (approx n) (approx n) w) v) rho)) lb.

(* A is the type of the abstract data. T is the type quantified over in the postcondition.
   W is the TypeTree of the witness for the rest of the function. *)
Program Definition atomic_spec {A T} W (a0 : A) args tz la Pp a (t : T) lb Qp b
  (Hla : super_non_expansive_la la) (HPp : super_non_expansive' Pp) (Ha : super_non_expansive_a a)
  (Hlb : super_non_expansive_lb lb) (HQp : super_non_expansive_b Qp) (Hb : super_non_expansive_b b) :=
  mk_funspec (pair args tz) cc_default (atomic_spec_type A W T)
  (fun (ts: list Type) '(w, P, Q, R, II, lI) =>
    PROP (atomic_shift P (a ts w) R (map II lI) (b ts w) Q)
    (LOCALx (map (fun l => l ts w) la)
    (SEP (Pp ts w; fold_right sepcon emp (map (fun p => invariant (II p)) lI); P))))
  (fun (ts: list Type) '(w, P, Q, R, II, lI) => EX v : T, EX x : A,
    PROP () (LOCALx (map (fun l => l ts w v) lb)
    (SEP (Qp ts w x v; fold_right sepcon emp (map (fun p => invariant (II p)) lI); Q x v)))) _ _.
Next Obligation.
Proof.
  replace _ with (fun (ts : list Type) (x : _ * mpred * (A -> T -> mpred) * (A -> mpred) * _ * list Z) rho =>
    PROP (let '(x, P, Q, R, II, lI) := x in atomic_shift P (a ts x) R (map II lI) (b ts x) Q)
    (LOCALx (map (fun Q0 => Q0 ts x) (map (fun l ts x => let '(x, P, Q, R, lI, II) := x in l ts x) la))
     SEP (let '(x, P, Q, R, II, lI) := x in
          Pp ts x * fold_right sepcon emp (map (fun p => invariant (II p)) lI) * P)) rho).
  apply (PROP_LOCAL_SEP_super_non_expansive (atomic_spec_type A W T) [fun _ => _]
    (map (fun l ts x => let '(x, P, Q, R, II, lI) := x in l ts x) la) [fun _ => _]);
    repeat constructor; hnf; intros; try destruct x as (((((x, P), Q), R), II), lI); auto; simpl.
  - unfold atomic_shift.
    rewrite !prop_and, !approx_andp; f_equal.
    + rewrite sepcon_comm, (sepcon_comm _ (_ _ P)).
      unfold view_shift_iff.
      rewrite !prop_and, !approx_andp; f_equal; rewrite view_shift_super_non_expansive;
        setoid_rewrite view_shift_super_non_expansive at 2.
      * setoid_rewrite (approx_sepcon_list _ (P :: _)); [|discriminate].
        setoid_rewrite (approx_sepcon_list _ (_ _ P :: _)); [|discriminate]; simpl.
        rewrite approx_idem; do 2 apply f_equal; f_equal.
        { erewrite !map_map, map_ext; eauto.
          intros; simpl; rewrite approx_idem; auto. }
        rewrite !approx_exp; apply f_equal; extensionality; rewrite !approx_sepcon, !approx_idem, Ha; auto.
      * setoid_rewrite (approx_sepcon_list _ (P :: _)); [|discriminate].
        setoid_rewrite (approx_sepcon_list _ (_ _ P :: _)); [|discriminate]; simpl.
        rewrite approx_idem; do 2 apply f_equal; f_equal.
        rewrite !approx_exp; apply f_equal; extensionality; rewrite !approx_sepcon, !approx_idem, Ha; auto.
        { erewrite !map_map, map_ext; eauto.
          intros; simpl; rewrite approx_idem; auto. }
    + rewrite !prop_forall, !approx_allp by auto.
      apply f_equal; extensionality.
      rewrite !prop_forall, !approx_allp by auto.
      apply f_equal; extensionality.
      rewrite view_shift_super_non_expansive.
      setoid_rewrite view_shift_super_non_expansive at 2.
      rewrite !approx_sepcon, !approx_sepcon_list'.
      erewrite !approx_idem, Hb, !map_map, map_ext; eauto.
      intros; simpl; rewrite approx_idem; auto.
  - rewrite Forall_forall; intros ? Hin.
    rewrite in_map_iff in Hin; destruct Hin as (? & ? & Hin); subst.
    intros ?? (((((x, P), Q), R), ?), ?) ?.
    specialize (Hla n ts x rho); rewrite Forall_forall in Hla; apply (Hla _ Hin).
  - rewrite !sepcon_assoc, !(approx_sepcon (Pp _ _)), HPp; apply f_equal.
    rewrite !approx_sepcon, !approx_sepcon_list'.
    erewrite approx_idem, !map_map, map_ext; eauto.
    intros; simpl; rewrite invariant_super_non_expansive; auto.
  - extensionality ts x rho.
    destruct x as (((((?, ?), ?), ?), ?), ?).
    unfold SEPx; simpl; rewrite map_map, !sepcon_assoc; auto.
Qed.
Next Obligation.
Proof.
  replace _ with (fun (ts : list Type)
    (w : _ * mpred * (A -> T -> mpred) * (A -> mpred) * (Z -> mpred) * _) rho =>
    EX v : T, EX x : A, PROP ()
    (LOCALx (map (fun Q0 => Q0 ts w) (map (fun l ts w => let '(w, P, Q, R, II, lI) := w in l ts w v) lb))
     SEP (let '(w, P, Q, R, II, lI) := w in
          Qp ts w x v * fold_right sepcon emp (map (fun p => invariant (II p)) lI) * Q x v)) rho).
  repeat intro.
  rewrite !approx_exp; apply f_equal; extensionality v.
  rewrite !approx_exp; apply f_equal; extensionality x1.
  apply (PROP_LOCAL_SEP_super_non_expansive (atomic_spec_type A W T) []
    (map (fun l ts w => let '(w, P, Q, R, II, lI) := w in l ts w v) lb)
    [fun ts w => let '(w, P, Q, R, II, lI) := w in
       Qp ts w x1 v * fold_right sepcon emp (map (fun p => invariant (II p)) lI) * Q x1 v]);
    repeat constructor; hnf; intros; try destruct x0 as (((((x0, P), Q), R), ?), ?); auto; simpl.
  - rewrite Forall_forall; intros ? Hin.
    rewrite in_map_iff in Hin; destruct Hin as (? & ? & Hin); subst.
    intros ?? (((((x', P), Q), R), ?), ?) ?.
    specialize (Hlb n0 ts0 x' v rho0); rewrite Forall_forall in Hlb; apply (Hlb _ Hin).
  - rewrite !sepcon_assoc, !(approx_sepcon (Qp _ _ _ _)), HQp; apply f_equal.
    rewrite !approx_sepcon, !approx_sepcon_list'.
    erewrite approx_idem, !map_map, map_ext; eauto.
    intros; simpl; rewrite invariant_super_non_expansive; auto.
  - extensionality ts x rho.
    destruct x as (((((?, ?), ?), ?), ?), ?).
    apply f_equal; extensionality.
    apply f_equal; extensionality.
    unfold SEPx; simpl; rewrite map_map, !sepcon_assoc; auto.
Qed.

End atomicity.

End atomics.

Ltac start_atomic_function :=
  match goal with |- semax_body ?V ?G ?F ?spec =>
    let s := fresh "spec" in
    pose (s:=spec); hnf in s;
    match goal with
    | s :=  (DECLARE _ WITH u : unit
               PRE  [] main_pre _ nil u
               POST [ tint ] main_post _ nil u) |- _ => idtac
    | s := ?spec' |- _ => check_canonical_funspec spec'
   end;
   change (semax_body V G F s); subst s
 end; unfold atomic_spec;
 let DependedTypeList := fresh "DependedTypeList" in
 match goal with |- semax_body _ _ _ (pair _ (mk_funspec _ _ _ ?Pre _ _ _)) =>
   match Pre with 
   | (fun x => match x with (a,b) => _ end) => intros Espec DependedTypeList [a b] 
   | (fun i => _) => intros Espec DependedTypeList (((((x, P), Q), R), II), lI)
   end;
   simpl fn_body; simpl fn_params; simpl fn_return
 end;
 simpl functors.MixVariantFunctor._functor in *;
 simpl rmaps.dependent_type_functor_rec;
 repeat match goal with |- @semax _ _ _ (match ?p with (a,b) => _ end * _) _ _ =>
             destruct p as [a b]
           end;
 simplify_func_tycontext;
 repeat match goal with 
 | |- context [Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s) Sskip] =>
       fold (Swhile e s)
 | |- context [Ssequence ?s1 (Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s2) ?s3) ] =>
      match s3 with
      | Sset ?i _ => match s1 with Sset ?i' _ => unify i i' | Sskip => idtac end
      end;
      fold (Sfor s1 e s2 s3)
 end;
 try expand_main_pre;
 process_stackframe_of;
 repeat change_mapsto_gvar_to_data_at;  (* should really restrict this to only in main,
                                  but it needs to come after process_stackframe_of *)
 repeat rewrite <- data_at__offset_zero;
 try apply start_function_aux1;
 repeat (apply semax_extract_PROP; 
              match goal with
              | |- _ ?sh -> _ =>
                 match type of sh with
                 | share => intros ?SH 
                 | Share.t => intros ?SH 
                 | _ => intro
                 end
               | |- _ => intro
               end);
 first [ eapply eliminate_extra_return'; [ reflexivity | reflexivity | ]
        | eapply eliminate_extra_return; [ reflexivity | reflexivity | ]
        | idtac];
 abbreviate_semax; simpl.

Hint Resolve emp_duplicable sepcon_duplicable invariant_duplicable ghost_snap_duplicable prop_duplicable : dup.

Hint Resolve emp_objective data_at_objective ghost_objective prop_objective andp_objective exp_objective
  sepcon_objective sepcon_list_objective : objective.
