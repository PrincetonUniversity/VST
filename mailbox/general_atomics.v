Require Import VST.veric.rmaps.
Require Import VST.veric.compcert_rmaps.
Require Import VST.progs.ghosts.
Require Import VST.progs.conclib.
Require Import VST.progs.invariants.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.
Require Export Ensembles.

Set Bullet Behavior "Strict Subproofs".

Arguments Empty_set {_}.
Arguments Full_set {_}.
Arguments Singleton {_} _.
Arguments Union {_} _ _.
Arguments Add {_} _ _.
Arguments Intersection {_} _ _.
Arguments Setminus {_} _ _.
Arguments Subtract {_} _ _.
Arguments Included {_} _ _.

(* invariants and fancy updates *)

(* Thoughts on invariants and the two-level structure:
   I expect that our version of the operational semantics will keep nonatomic locations as is,
   so that the points-to assertions won't need view parameters (and in fact will be objective?).
   The question then is: do we need the two-level structure in which iGPS-style assertions are
   functions from view to mpred, or can even protocol assertions simply be mpreds? We might be able
   to use something like the external state construction to use ghost state to remember per-thread
   timestamps, so that we don't need to include timestamps in the rmap (or as an extra argument
   to assertions). In this model, there would be no objectivity requirement at all: instead,
   protocol assertions from other threads would be incompatible with the current thread because
   they refer to a different location for their timestamp ghost state.
   On the other hand, if we do need the two-level structure, we should still define invariants
   without objectivity here (as Iris-level invariants), and define iGPS-level invariants elsewhere. *)
(* We will still, of course, have to choose between SC and RA atomics in any given proof/program,
   since there's no soundness proof (or operational model) for a language with both. And invariants
   must still be accessible only via atomics. Does this make the fancy-update style useless,
   since we can't insert it into the definition of semax? Well, iGPS still uses it in the RA atomic
   rules, so maybe it's still useful. *)

Parameter fupd : Ensemble namespace -> Ensemble namespace -> mpred -> mpred.

Notation "|={ E1 , E2 }=> P" := (fupd E1 E2 P) (at level 62): logic.
Notation "|={ E }=> P" := (fupd E E P) (at level 62): logic.

Axiom fupd_mono : forall E1 E2 P Q, P |-- Q -> |={E1, E2}=> P |-- |={E1, E2}=> Q.
Axiom bupd_fupd : forall E P, |==> P |-- |={E}=> P.
Axiom fupd_frame_r : forall E1 E2 P Q, fupd E1 E2 P * Q |-- fupd E1 E2 (P * Q).
Axiom fupd_intro_mask : forall E1 E2 P, Included E2 E1 -> P |-- |={E1,E2}=> |={E2,E1}=> P.
Axiom fupd_trans : forall E1 E2 E3 P, (|={E1,E2}=> |={E2,E3}=> P) |-- |={E1,E3}=> P.

Lemma fupd_frame_l : forall E1 E2 P Q, P * fupd E1 E2 Q |-- fupd E1 E2 (P * Q).
Proof.
  intros; rewrite sepcon_comm, (sepcon_comm P Q); apply fupd_frame_r.
Qed.

Lemma fupd_bupd : forall E1 E2 P Q, P |-- |==> (|={E1,E2}=> Q) -> P |-- |={E1,E2}=> Q.
Proof.
  intros; eapply derives_trans, fupd_trans; eapply derives_trans, bupd_fupd; auto.
Qed.

(* This is a generally useful pattern. *)
Lemma fupd_mono' : forall E1 E2 P Q (a : rmap) (Himp : (P >=> Q) (level a)),
  app_pred (fupd E1 E2 P) a -> app_pred (fupd E1 E2 Q) a.
Proof.
  intros.
  assert (app_pred ((|={E1,E2}=> P * approx (S (level a)) emp)) a) as HP'.
  { apply (fupd_frame_r _ _ _ _ a).
    do 3 eexists; [apply join_comm, core_unit | split; auto].
    split; [|apply core_identity].
    rewrite level_core; auto. }
  eapply fupd_mono in HP'; eauto.
  change (predicates_hered.derives (P * approx (S (level a)) emp) Q).
  intros a0 (? & ? & J & HP & [? Hemp]).
  destruct (join_level _ _ _ J).
  apply join_comm, Hemp in J; subst.
  eapply Himp in HP; try apply necR_refl; auto; omega.
Qed.

Definition timeless P := |>P |-- P || |>FF.

Definition timeless' (P : mpred) := forall (a a' : rmap), predicates_hered.app_pred P a' -> age a a' ->
  predicates_hered.app_pred P a.

Lemma timeless'_timeless : forall P, timeless' P -> timeless P.
Proof.
  unfold timeless; intros.
  change (_ |-- _) with (predicates_hered.derives (|>P) (P || |>FF)); intros ? HP.
  destruct (level a) eqn: Ha.
  - right; intros ? ?%laterR_level; omega.
  - left.
    destruct (levelS_age a n) as [b [Hb]]; auto.
    specialize (HP _ (semax_lemmas.age_laterR Hb)).
    eapply H; eauto.
Qed.

Lemma address_mapsto_timeless : forall m v sh p, timeless (res_predicates.address_mapsto m v sh p).
Proof.
  intros; apply timeless'_timeless.
  repeat intro.
  simpl in *.
  destruct H as (b & [? HYES] & ?); exists b; split; [split|]; auto.
  intro b'; specialize (HYES b').
  if_tac.
  - destruct HYES as (rsh & Ha'); exists rsh.
    erewrite age_to_resource_at.age_resource_at in Ha' by eauto.
    destruct (a @ b'); try discriminate; inv Ha'.
    destruct p0; inv H6; simpl.
    f_equal.
    apply proof_irr.
  - rewrite age1_resource_at_identity; eauto.
  - rewrite age1_ghost_of_identity; eauto.
Qed.

Axiom fupd_timeless : forall E P, timeless P -> |> P |-- |={E}=> P.

Axiom inv_alloc : forall N E P, |> P |-- |={E}=> invariant N P.

Corollary make_inv : forall N E P Q, P |-- Q -> P |-- |={E}=> invariant N Q.
Proof.
  intros.
  eapply derives_trans, inv_alloc; auto.
  eapply derives_trans, now_later; auto.
Qed.

Axiom inv_open : forall (E : Ensemble namespace) N P, E N ->
  invariant N P |-- |={E, Subtract E N}=> (|> P) * (|>P -* |={Subtract E N, E}=> emp).

Axiom invariant_precise : forall N P, precise (invariant N P).

Axiom invariant_super_non_expansive : forall n N P, approx n (invariant N P) =
approx n (invariant N (approx n P)).

Axiom invariant_duplicable : forall N P, invariant N P = invariant N P * invariant N P.

Section atomics.

Context {CS : compspecs}.

Section dup.

Definition duplicable P := P |-- |==> P * P.

Lemma emp_duplicable : duplicable emp.
Proof.
  unfold duplicable.
  rewrite sepcon_emp; apply bupd_intro.
Qed.
Hint Resolve emp_duplicable : dup.

Lemma sepcon_duplicable : forall P Q, duplicable P -> duplicable Q -> duplicable (P * Q).
Proof.
  intros; unfold duplicable.
  rewrite <- sepcon_assoc, (sepcon_comm (_ * Q)), <- sepcon_assoc, sepcon_assoc.
  eapply derives_trans, bupd_sepcon.
  apply sepcon_derives; auto.
Qed.
Hint Resolve sepcon_duplicable : dup.

Lemma sepcon_list_duplicable : forall lP, Forall duplicable lP -> duplicable (fold_right sepcon emp lP).
Proof.
  induction 1; simpl; auto with dup.
Qed.

Lemma list_duplicate : forall Q lP, duplicable Q ->
  fold_right sepcon emp lP * Q |-- |==> fold_right sepcon emp (map (sepcon Q) lP) * Q.
Proof.
  induction lP; simpl; intros; [apply bupd_intro|].
  rewrite sepcon_assoc; eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply IHlP]; auto|].
  eapply derives_trans; [apply sepcon_derives, bupd_mono, sepcon_derives, H; apply derives_refl|].
  eapply derives_trans; [apply bupd_frame_l|].
  eapply derives_trans, bupd_trans.
  apply bupd_mono; cancel.
  eapply derives_trans; [apply bupd_frame_l|].
  apply bupd_mono; cancel.
Qed.

(* Should all duplicables be of this form? *)
Lemma invariant_duplicable' : forall N P, duplicable (invariant N P).
Proof.
  unfold duplicable; intros.
  rewrite <- invariant_duplicable in *; apply bupd_intro.
Qed.
Hint Resolve invariant_duplicable' : dup.

Lemma ghost_snap_duplicable : forall `{_ : PCM_order} (s : G) p, duplicable (ghost_snap s p).
Proof.
  intros; unfold duplicable.
  erewrite ghost_snap_join; [apply bupd_intro|].
  apply join_refl.
Qed.
Hint Resolve ghost_snap_duplicable : dup.

Lemma prop_duplicable : forall P Q, duplicable Q -> duplicable (!!P && Q).
Proof.
  intros; unfold duplicable.
  Intros.
  rewrite prop_true_andp; auto.
Qed.
Hint Resolve prop_duplicable : dup.

Lemma exp_duplicable : forall {A} (P : A -> mpred), (forall x, duplicable (P x)) -> duplicable (exp P).
Proof.
  unfold duplicable; intros.
  Intro x.
  eapply derives_trans; eauto.
  apply bupd_mono; Exists x x; auto.
Qed.

Definition weak_dup P := weak_view_shift P (P * P).

Lemma duplicable_super_non_expansive : forall n P,
  approx n (weak_dup P) = approx n (weak_dup (approx n P)).
Proof.
  intros; unfold weak_dup.
  rewrite view_shift_nonexpansive, approx_sepcon; auto.
Qed.

Lemma dup_weak_dup : forall P, duplicable P -> TT |-- weak_dup P.
Proof.
  intros; apply view_shift_weak; auto.
Qed.

End dup.

Definition AL_type := ProdType (ProdType (ProdType (ProdType (ProdType (ConstType val) Mpred)
  (ArrowType (ConstType Z) Mpred)) (ConstType (list Z)))
  (ArrowType (ConstType share) (ArrowType (ConstType Z) Mpred))) (ArrowType (ConstType Z) Mpred).

(*Program Definition load_SC_spec := TYPE AL_type
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

Definition AEX_type := ProdType (ProdType (ProdType (ProdType (ProdType (ConstType (val * Z)) Mpred)
  (ArrowType (ConstType Z) Mpred)) (ConstType (list Z)))
  (ArrowType (ConstType share) (ArrowType (ConstType Z) Mpred))) (ArrowType (ConstType Z) Mpred).

Program Definition AEX_SC_spec := TYPE AEX_type
  WITH p : val, v : Z, P : mpred, II : Z -> mpred, lI : list Z, P' : share -> Z -> mpred,
       Q : Z -> mpred
  PRE [ 1%positive OF tptr tint, 2%positive OF tint ]
   PROP (repable_signed v;
         view_shift (fold_right sepcon emp (map II lI) * P)
           (EX sh : share, EX v0 : Z, !!(writable_share sh /\ repable_signed v0) &&
              data_at sh tint (vint v0) p * P' sh v0);
         forall sh v0, view_shift (!!(writable_share sh /\ repable_signed v0) &&
           data_at sh tint (vint v) p * P' sh v0)
           (fold_right sepcon emp (map II lI) * Q v0))
   LOCAL (temp 1%positive p; temp 2%positive (vint v))
   SEP (fold_right sepcon emp (map (fun p => invariant (II p)) lI); P)
  POST [ tint ]
   EX v' : Z,
   PROP (repable_signed v')
   LOCAL (temp ret_temp (vint v'))
   SEP (fold_right sepcon emp (map (fun p => invariant (II p)) lI); Q v').
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
  destruct x as ((((((?, ?), ?), ?), ?), ?), ?); simpl.
  rewrite !approx_exp; apply f_equal; extensionality vr.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem.
  rewrite !approx_sepcon_list'.
  erewrite !map_map, map_ext; eauto.
  intros; simpl; rewrite invariant_super_non_expansive; auto.
Qed.*)

Section atomicity.

(* weak view shift for use in funspecs *)
Program Definition weak_fview_shift E1 E2 (P Q: mpred): mpred :=
  fun w => predicates_hered.derives (approx (S (level w)) P) (fupd E1 E2 (approx (S (level w)) Q)).
Next Obligation.
  repeat intro.
  destruct H1.
  apply age_level in H.
  lapply (H0 a0); [|split; auto; omega].
  apply fupd_mono'.
  change ((approx (S (level a)) Q >=> approx (S (level a')) Q)%pred (level a0)).
  intros ????%necR_level [].
  repeat split; auto; omega.
Qed.

(* up *)
Lemma approx_mono: forall n P Q, (P >=> Q) (Nat.pred n) -> approx n P |-- approx n Q.
Proof.
  intros.
  change (predicates_hered.derives (approx n P) (approx n Q)).
  intros ? [? HP]; split; auto.
  eapply H in HP; eauto; omega.
Qed.

Lemma fview_shift_nonexpansive: forall E1 E2 P Q n,
  approx n (weak_fview_shift E1 E2 P Q) = approx n (weak_fview_shift E1 E2 (approx n P) (approx n Q)).
Proof.
  intros ??; apply nonexpansive2_super_non_expansive; repeat intro.
  - split; intros ??%necR_level Hshift; simpl in *; eapply predicates_hered.derives_trans; eauto;
      apply fupd_mono, approx_mono; simpl.
    + change ((P0 >=> Q)%pred (level a')).
      intros ????%necR_level ?; eapply H; try apply necR_refl; auto; omega.
    + change ((Q >=> P0)%pred (level a')).
      intros ????%necR_level ?; eapply H; try apply necR_refl; auto; omega.
  - split; intros ??%necR_level Hshift; simpl in *; eapply predicates_hered.derives_trans, Hshift;
      apply approx_mono; simpl.
    + change ((Q0 >=> P)%pred (level a')).
      intros ????%necR_level ?; eapply H; try apply necR_refl; auto; omega.
    + change ((P >=> Q0)%pred (level a')).
      intros ????%necR_level ?; eapply H; try apply necR_refl; auto; omega.
Qed.

Lemma fview_shift_weak: forall E1 E2 P Q, (P |-- |={E1, E2}=> Q) -> TT |-- weak_fview_shift E1 E2 P Q.
Proof.
  intros.
  change (predicates_hered.derives TT (weak_fview_shift E1 E2 P Q)).
  intros a _ a0 [? HP].
  apply H in HP.
  eapply fupd_mono'; eauto.
  change ((Q >=> approx (S (level a)) Q)%pred (level a0)).
  intros ????%necR_level ?; split; auto; omega.
Qed.

Lemma apply_fview_shift: forall E1 E2 P Q, (weak_fview_shift E1 E2 P Q && emp) * P |-- |={E1, E2}=> Q.
Proof.
  intros.
  change (predicates_hered.derives ((weak_fview_shift E1 E2 P Q && emp) * P) (fupd E1 E2 Q)).
  intros ? (? & ? & ? & [Hshift Hemp] & HP).
  destruct (join_level _ _ _ H).
  apply Hemp in H; subst.
  lapply (Hshift a); [|split; auto; omega].
  apply fupd_mono'.
  change (((approx (S (level x)) Q) >=> Q)%pred (level a)).
  intros ???? []; auto.
Qed.

(* The logical atomicity of Iris. *)
Definition atomic_shift {A B} (a : A -> mpred) Ei Eo (b : A -> B -> mpred) (Q : B -> mpred) :=
  EX P : mpred, |> P * (weak_fview_shift Eo Ei (|> P) (EX x : A, a x *
    ((weak_fview_shift Ei Eo (a x) (|> P) && emp) &&
    ALL y : B, weak_fview_shift Ei Eo (b x y) (Q y) && emp)) && emp).

Definition atomic_spec_type W T := ProdType W (ArrowType (ConstType T) Mpred).

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
Program Definition atomic_spec {A T} W args tz la P a (t : T) lb b Ei Eo
  (Hla : super_non_expansive_la la) (HP : super_non_expansive' P) (Ha : super_non_expansive_a(A := A) a)
  (Hlb : super_non_expansive_lb lb) (Hb : super_non_expansive_b b) :=
  mk_funspec (pair args tz) cc_default (atomic_spec_type W T)
  (fun (ts: list Type) '(w, Q) =>
    PROP ()
    (LOCALx (map (fun l => l ts w) la)
    (SEP (atomic_shift (a ts w) Ei Eo (b ts w) Q; P ts w))))
  (fun (ts: list Type) '(w, Q) => EX v : T,
    PROP () (LOCALx (map (fun l => l ts w v) lb)
    (SEP (Q v)))) _ _.
Next Obligation.
Proof.
  replace _ with (fun (ts : list Type) (x : _ * (T -> mpred)) rho =>
    PROP ()
    (LOCALx (map (fun Q0 => Q0 ts x) (map (fun l ts x => let '(x, Q) := x in l ts x) la))
     SEP (let '(x, Q) := x in
          atomic_shift (a ts x) Ei Eo (b ts x) Q * P ts x)) rho).
  apply (PROP_LOCAL_SEP_super_non_expansive (atomic_spec_type W T) []
    (map (fun l ts x => let '(x, Q) := x in l ts x) la) [fun _ => _]);
    repeat constructor; hnf; intros; try destruct x as (x, Q); auto; simpl.
  - rewrite Forall_forall; intros ? Hin.
    rewrite in_map_iff in Hin; destruct Hin as (? & ? & Hin); subst.
    intros ?? (x, Q) ?.
    specialize (Hla n ts x rho); rewrite Forall_forall in Hla; apply (Hla _ Hin).
  - unfold atomic_shift.
    rewrite !approx_sepcon; f_equal; auto.
    rewrite !approx_exp; f_equal; extensionality.
    rewrite !approx_sepcon, !approx_andp; f_equal; f_equal.
    rewrite fview_shift_nonexpansive.
    setoid_rewrite fview_shift_nonexpansive at 2; f_equal; f_equal.
    rewrite !approx_exp; f_equal; extensionality.
    rewrite !approx_sepcon, !approx_andp; f_equal; auto.
    f_equal.
    + rewrite fview_shift_nonexpansive.
      setoid_rewrite fview_shift_nonexpansive at 2; f_equal; f_equal; f_equal; auto.
    + rewrite !approx_allp by auto; f_equal; extensionality.
      rewrite !approx_andp; f_equal.
      rewrite fview_shift_nonexpansive.
      setoid_rewrite fview_shift_nonexpansive at 2; f_equal; f_equal; auto.
      rewrite approx_idem; auto.
  - extensionality ts x rho.
    destruct x.
    unfold SEPx; simpl; rewrite map_map, !sepcon_assoc; auto.
Qed.
Next Obligation.
Proof.
  replace _ with (fun (ts : list Type) (w : _ * (T -> mpred)) rho =>
    EX v : T, PROP ()
    (LOCALx (map (fun Q0 => Q0 ts w) (map (fun l ts w => let '(w, Q) := w in l ts w v) lb))
     SEP (let '(w, Q) := w in Q v)) rho).
  repeat intro.
  rewrite !approx_exp; apply f_equal; extensionality v.
  apply (PROP_LOCAL_SEP_super_non_expansive (atomic_spec_type W T) []
    (map (fun l ts w => let '(w, Q) := w in l ts w v) lb)
    [fun ts w => let '(w, Q) := w in Q v]);
    repeat constructor; hnf; intros; try destruct x0 as (x0, Q); auto; simpl.
  - rewrite Forall_forall; intros ? Hin.
    rewrite in_map_iff in Hin; destruct Hin as (? & ? & Hin); subst.
    intros ?? (x', Q) ?.
    specialize (Hlb n0 ts0 x' v rho0); rewrite Forall_forall in Hlb; apply (Hlb _ Hin).
  - rewrite approx_idem; auto.
  - extensionality ts x rho.
    destruct x.
    apply f_equal; extensionality.
    unfold SEPx; simpl; rewrite map_map; auto.
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
   | (fun i => _) => intros Espec DependedTypeList (x, Q)
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

(*Notation store_SC_witness p v P II lI Q := (p, v%Z, P, II%function, lI%gfield,
  fun sh => !!(writable_share sh) && data_at sh tint (vint v) p -*
  fold_right sepcon emp (map II lI) * Q, Q).

Notation AEX_SC_witness p v P II lI Q := (p, v%Z, P, II%function, lI%gfield,
  fun sh v0 => !!(writable_share sh /\ repable_signed v0) && data_at sh tint (vint v) p -*
  fold_right sepcon emp (map II lI) * Q v0, Q).

Notation load_SC_witness p P II lI Q := (p, P, II%function, lI%gfield,
  fun sh v => !!(readable_share sh /\ repable_signed v) && data_at sh tint (vint v) p -*
  fold_right sepcon emp (map II lI) * Q v, Q).

Notation CAS_SC_witness p c v P II lI Q := (p, c, v%Z, P, II%function, lI%gfield,
  fun sh v0 => !!(writable_share sh /\ repable_signed v0) &&
    data_at sh tint (vint (if eq_dec v0 c then v else v0)) p -*
  fold_right sepcon emp (map II lI) * Q v0, Q).*)
