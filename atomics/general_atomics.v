Require Import VST.veric.rmaps.
Require Import VST.veric.compcert_rmaps.
Require Import VST.progs.ghosts.
Require Import VST.progs.conclib.
Require Import VST.progs.invariants.
Require Import VST.progs.fupd.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.
Require Import iris.bi.lib.atomic.

Set Bullet Behavior "Strict Subproofs".

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

Section atomics.

Context {CS : compspecs} {inv_names : invG}.

Section atomicity.

(* The logical atomicity of Iris. *)
(* We use the cored predicate to mimic Iris's persistent modality. *)
Definition ashift {A B} P (a : A -> mpred) Ei Eo (b : A -> B -> mpred) (Q : B -> mpred) :=
  ((|> P -* |={Eo,Ei}=> (EX x : A, a x *
    ((a x -* |={Ei,Eo}=> |> P) &&
     ALL y : B, b x y -* |={Ei,Eo}=> Q y))))%I.

(* switch to Ralf's? *)
Locate atomic_update.

Definition atomic_shift {A B} (a : A -> mpred) Ei Eo (b : A -> B -> mpred) (Q : B -> mpred) :=
  EX P : mpred, |> P * (ashift P a Ei Eo b Q && cored).

Lemma atomic_commit_fupd : forall {A B} (a : A -> mpred) Ei Eo (b : A -> B -> mpred) (Q : B -> mpred) R R',
  (forall x, R * a x |-- |==> (EX y, b x y) * R')%I ->
  (atomic_shift a Ei Eo b Q * R |-- |={Eo}=> (EX y, Q y) * R')%I.
Proof.
  intros.
  iIntros "[AS R]".
  unfold atomic_shift, ashift.
  iDestruct "AS" as (P) "[P AS]".
  iMod ("AS" with "P") as (x) "[a [_ H]]".
  iMod (H with "[$R $a]") as "[b $]".
  iDestruct "b" as (y) "b"; iExists y.
  iMod ("H" with "b") as "$"; auto.
Qed.

Corollary atomic_commit_elim : forall {A B} (a : A -> mpred) Ei Eo (b : A -> B -> mpred) (Q : B -> mpred) R R',
  (forall x, R * a x |-- |==> (EX y, b x y) * R')%I ->
  (wsat * ghost_set g_en (coPset_to_Ensemble Eo) * atomic_shift a Ei Eo b Q * R |-- |==> ◇ (wsat * ghost_set g_en (coPset_to_Ensemble Eo) * ((EX y, Q y) * R')))%I.
Proof.
  intros.
  iIntros "[[[wsat en] AS] R]".
  iApply wsat_fupd_elim'; iFrame.
  iApply atomic_commit_fupd; eauto; iFrame.
Qed.

(* This is unsound: what we really need is fupd in WP. *)
Lemma atomic_commit : forall {A B} (a : A -> mpred) Ei Eo (b : A -> B -> mpred) (Q : B -> mpred) R R',
  (forall x, R * a x |-- |==> (EX y, b x y) * R')%I ->
  (atomic_shift a Ei Eo b Q * R |-- |==> (EX y, Q y) * R')%I.
Proof.
  intros.
  eapply atomic_commit_elim in H.
  admit.
Admitted.

Lemma atomic_shift_mask_weaken {A B} Eo1 Eo2 Ei a (b : A -> B -> mpred) Q :
  Eo1 ⊆ Eo2 ->
  atomic_shift a Ei Eo1 b Q |-- atomic_shift a Ei Eo2 b Q.
Proof.
  intros; unfold atomic_shift, ashift.
  Intros P; Exists P; cancel.
  apply andp_derives; auto.
  apply wand_derives; auto.
  iIntros "H".
  iMod (updates.fupd_intro_mask Eo2 Eo1 emp with "[]") as "mask"; auto.
  iMod "H" as (x) "[Ha Hb]".
  iExists x; iFrame.
  iIntros "!>"; iSplit.
  - iIntros "a"; iMod ("Hb" with "a") as "$"; auto.
  - iIntros (y) "b"; iMod ("Hb" with "b") as "$"; auto.
Qed.

Lemma inv_atomic_shift : forall {A B} a Ei Eo (b : A -> B -> mpred) Q i R P
  (Hi : inv i ⊆ Eo) (Hio : Ei ⊆ Eo ∖ inv i)
  (Ha1 : (|>R |-- |={Eo ∖ inv i}=> EX x, a x * ((a x -* |={Eo ∖ inv i}=> |>R) &&
    (ALL y, |> P * b x y -* |={Eo ∖ inv i}=> |>R * Q y)))%I),
  invariant i R * P |-- atomic_shift a Ei Eo b Q.
Proof.
  intros; unfold atomic_shift.
  Exists P; cancel.
  apply andp_right, invariant_cored.
  unfold ashift.
  iIntros "I P".
  iMod (inv_open with "I") as "[R Hclose]"; first done.
  iMod (Ha1 with "R") as (x) "[a R]".
  iExists x; iFrame.
  iMod (updates.fupd_intro_mask (Eo ∖ inv i) Ei emp with "[]") as "mask"; auto.
  iIntros "!>"; iSplit.
  - iIntros "a"; iFrame.
    iMod "mask" as "_".
    iMod ("R" with "a").
    iApply "Hclose"; auto.
  - iIntros (y) "b".
    iMod "mask" as "_".
    iMod ("R" with "[$P $b]") as "[R $]".
    iApply "Hclose"; auto.
Qed.

Lemma ashift_nonexpansive : forall {A B} P n a Ei Eo (b : A -> B -> mpred) Q,
  approx n (ashift P a Ei Eo b Q) =
  approx n (ashift P (fun x => approx n (a x)) Ei Eo (fun x y => approx n (b x y)) (fun y => approx n (Q y))).
Proof.
  intros; unfold ashift.
  setoid_rewrite fview_shift_nonexpansive; f_equal; f_equal; f_equal.
  rewrite !approx_exp; f_equal; extensionality.
  rewrite -> !approx_sepcon, !approx_andp, !approx_idem; f_equal; auto.
  f_equal.
  * setoid_rewrite fview_shift_nonexpansive; rewrite !approx_idem; f_equal; f_equal; auto.
  * rewrite allp_nonexpansive; setoid_rewrite allp_nonexpansive at 2; f_equal; f_equal; extensionality.
    setoid_rewrite fview_shift_nonexpansive; rewrite !approx_idem; auto.
Qed.

Lemma atomic_shift_nonexpansive : forall {A B} n a Ei Eo (b : A -> B -> mpred) Q,
  approx n (atomic_shift a Ei Eo b Q) =
  approx n (atomic_shift (fun x => approx n (a x)) Ei Eo (fun x y => approx n (b x y)) (fun y => approx n (Q y))).
Proof.
  intros; unfold atomic_shift.
  rewrite !approx_exp; f_equal; extensionality.
  rewrite !approx_sepcon !approx_andp ashift_nonexpansive; auto.
Qed.

Lemma atomic_shift_derives_frame_cored : forall {A A' B B'} (a : A -> mpred) (a' : A' -> mpred) Ei Eo
  (b : A -> B -> mpred) (b' : A' -> B' -> mpred) (Q : B -> mpred) (Q' : B' -> mpred) F R
  (HF : F |-- cored)
  (Ha : (forall x, a x * F * |>R |-- |={Ei}=> EX x' : A', a' x' *
    ((a' x' -* |={Ei}=> a x * |>R) && ALL y' : _, b' x' y' -* |={Ei}=> EX y : _, b x y * (Q y -* |={Eo}=> Q' y')))%I),
  atomic_shift a Ei Eo b Q * F * |>R |-- atomic_shift a' Ei Eo b' Q'.
Proof.
  intros; unfold atomic_shift, ashift.
  Intros P; Exists (P * R); rewrite later_sepcon; cancel.
  erewrite (add_andp F) by apply HF.
  sep_apply cored_sepcon.
  apply andp_derives; auto.
  iIntros "[H F] [P R]"; iMod ("H" with "P") as (x) "[a H]".
  iMod (Ha with "[$a $F $R]") as (x') "[? Hrest]"; iExists x'; iFrame.
  iIntros "!>"; iSplit.
  - iIntros "a".
    iDestruct "Hrest" as "[Hrest _]".
    iMod ("Hrest" with "a") as "[? $]"; iApply "H"; auto.
  - iIntros (y') "b".
    iDestruct "Hrest" as "[_ Hb]".
    iMod ("Hb" $! y' with "b") as (y) "[b HQ]".
    iMod ("H" with "b").
    iApply "HQ"; auto.
Qed.

Lemma atomic_shift_derives_frame : forall {A A' B B'} (a : A -> mpred) (a' : A' -> mpred) Ei Eo
  (b : A -> B -> mpred) (b' : A' -> B' -> mpred) (Q : B -> mpred) (Q' : B' -> mpred) R
  (Ha : (forall x, a x * |>R |-- |={Ei}=> EX x' : A', a' x' *
    ((a' x' -* |={Ei}=> a x * |>R) && ALL y' : _, b' x' y' -* |={Ei}=> EX y : _, b x y * (Q y -* |={Eo}=> Q' y')))%I),
  atomic_shift a Ei Eo b Q * |>R |-- atomic_shift a' Ei Eo b' Q'.
Proof.
  intros; unfold atomic_shift, ashift.
  Intros P; Exists (P * R); rewrite later_sepcon; cancel.
  apply andp_derives; auto.
  iIntros "H [P R]"; iMod ("H" with "P") as (x) "[a H]".
  iMod (Ha with "[$a $R]") as (x') "[? Hrest]"; iExists x'; iFrame.
  iIntros "!>"; iSplit.
  - iIntros "a".
    iMod ("Hrest" with "a") as "[? $]"; iApply "H"; auto.
  - iIntros (y') "b".
    iDestruct "Hrest" as "[_ Hb]".
    iMod ("Hb" $! y' with "b") as (y) "[b HQ]".
    iMod ("H" with "b").
    iApply "HQ"; auto.
Qed.

Lemma ashift_derives : forall {A A' B B'} P (a : A -> mpred) (a' : A' -> mpred) Ei Eo
  (b : A -> B -> mpred) (b' : A' -> B' -> mpred) (Q : B -> mpred) (Q' : B' -> mpred)
  (Ha : (forall x, a x  |-- |={Ei}=> EX x' : A', a' x' *
    (((a' x' * (ashift P a Ei Eo b Q && cored)) -* |={Ei}=> a x) &&
     ALL y' : _, (b' x' y' * (ashift P a Ei Eo b Q && cored)) -* |={Ei}=> EX y : _, b x y * (Q y -* |={Eo}=> Q' y')))%I),
  (ashift P a Ei Eo b Q && cored |-- ashift P a' Ei Eo b' Q' && cored)%logic.
Proof.
  intros.
  sep_apply cored_dup_cored.
  apply andp_derives; auto.
  unfold ashift at 1 3.
  iIntros "[H AS] P"; iMod ("H" with "P") as (x) "[a H]".
  iMod (Ha with "a") as (x') "[? Hrest]"; iExists x'; iFrame.
  iIntros "!>"; iSplit.
  - iIntros "a".
    iDestruct "Hrest" as "[Hrest _]".
    iMod ("Hrest" with "[$a $AS]") as "a"; iApply "H"; auto.
  - iIntros (y') "b".
    iDestruct "Hrest" as "[_ Hb]".
    iMod ("Hb" $! y' with "[$b $AS]") as (y) "[b HQ]".
    iMod ("H" with "b").
    iApply "HQ"; auto.
Qed.

Lemma atomic_shift_derives : forall {A A' B B'} (a : A -> mpred) (a' : A' -> mpred) Ei Eo
  (b : A -> B -> mpred) (b' : A' -> B' -> mpred) (Q : B -> mpred) (Q' : B' -> mpred)
  (Ha : (forall x, a x  |-- |={Ei}=> EX x' : A', a' x' *
    ((a' x' -* |={Ei}=> a x) && ALL y' : _, b' x' y' -* |={Ei}=> EX y : _, b x y * (Q y -* |={Eo}=> Q' y')))%I),
  atomic_shift a Ei Eo b Q |-- atomic_shift a' Ei Eo b' Q'.
Proof.
  intros; eapply derives_trans, atomic_shift_derives_frame.
  { rewrite <- sepcon_emp at 1; apply sepcon_derives; [apply derives_refl | apply now_later]. }
  iIntros (x) "[a >_]".
  iMod (Ha with "a") as (x') "[? H]".
  iExists x'; iFrame; iIntros "!>"; iSplit.
  - iIntros "a"; iMod ("H" with "a") as "$"; auto.
  - iDestruct "H" as "[_ H]"; auto.
Qed.

Lemma atomic_shift_derives_cored : forall {A A' B B'} (a : A -> mpred) (a' : A' -> mpred) Ei Eo
  (b : A -> B -> mpred) (b' : A' -> B' -> mpred) (Q : B -> mpred) (Q' : B' -> mpred) F
  (HF : F |-- cored)
  (Ha : (forall x, a x * F |-- |={Ei}=> EX x' : A', a' x' *
    ((a' x' -* |={Ei}=> a x) && ALL y' : _, b' x' y' -* |={Ei}=> EX y : _, b x y * (Q y -* |={Eo}=> Q' y')))%I),
  atomic_shift a Ei Eo b Q * F |-- atomic_shift a' Ei Eo b' Q'.
Proof.
  intros; eapply derives_trans, atomic_shift_derives_frame_cored; eauto.
  { rewrite <- sepcon_emp at 1; apply sepcon_derives; [apply derives_refl | apply now_later]. }
  iIntros (x) "[a >_]".
  iMod (Ha with "a") as (x') "[? H]".
  iExists x'; iFrame; iIntros "!>"; iSplit.
  - iIntros "a"; iMod ("H" with "a") as "$"; auto.
  - iDestruct "H" as "[_ H]"; auto.
Qed.

Lemma atomic_shift_derives' : forall {A A' B} (a : A -> mpred) (a' : A' -> mpred) Ei Eo
  (b : A -> B -> mpred) (b' : A' -> B -> mpred) (Q : B -> mpred)
  (Ha : (forall x, a x |-- |={Ei}=> EX x' : A', a' x' *
    ((a' x' -* |={Ei}=> a x) && ALL y : _, b' x' y -* |={Ei}=> b x y))%I),
  atomic_shift a Ei Eo b Q |-- atomic_shift a' Ei Eo b' Q.
Proof.
  intros; apply atomic_shift_derives.
  iIntros (x) "a"; iMod (Ha with "a") as (x') "[a H]".
  iExists x'; iFrame.
  iIntros "!>"; iSplit.
  - iIntros "a"; iMod ("H" with "a") as "$"; auto.
  - iIntros (y) "b"; iExists y.
    iDestruct "H" as "[_ H]".
    iMod ("H" with "b") as "$".
    iIntros "!> $"; auto.
Qed.

Lemma atomic_shift_derives'_cored : forall {A A' B} (a : A -> mpred) (a' : A' -> mpred) Ei Eo
  (b : A -> B -> mpred) (b' : A' -> B -> mpred) (Q : B -> mpred) F
  (HF : F |-- cored)
  (Ha : (forall x, a x * F |-- |={Ei}=> EX x' : A', a' x' *
    ((a' x' -* |={Ei}=> a x) && ALL y : _, b' x' y -* |={Ei}=> b x y))%I),
  atomic_shift a Ei Eo b Q * F |-- atomic_shift a' Ei Eo b' Q.
Proof.
  intros; apply atomic_shift_derives_cored; auto.
  iIntros (x) "a"; iMod (Ha with "a") as (x') "[a H]".
  iExists x'; iFrame.
  iIntros "!>"; iSplit.
  - iIntros "a"; iMod ("H" with "a") as "$"; auto.
  - iIntros (y) "b"; iExists y.
    iDestruct "H" as "[_ H]".
    iMod ("H" with "b") as "$".
    iIntros "!> $"; auto.
Qed.

Lemma atomic_shift_derives_simple : forall {A B} (a a' : A -> mpred) Ei Eo (b b' : A -> B -> mpred) (Q : B -> mpred)
  (Ha1 : (forall x, a x |-- |={Ei}=> a' x)%I)
  (Ha2 : (forall x, a' x |-- |={Ei}=> a x)%I)
  (Hb : (forall x y, b' x y |-- |={Ei}=> b x y)%I),
  atomic_shift a Ei Eo b Q |-- atomic_shift a' Ei Eo b' Q.
Proof.
  intros; apply atomic_shift_derives'; intros.
  iIntros "a"; iExists x; iMod (Ha1 with "a") as "$".
  iIntros "!>"; iSplit.
  - iApply Ha2.
  - iIntros (?); iApply Hb.
Qed.

Lemma atomic_shift_exists : forall {A B} a Ei Eo (b : A -> B -> mpred) Q,
  atomic_shift (fun (_ : unit) => EX x : A, a x) Ei Eo (fun (_ : unit) => EX x : A, b x) Q |-- atomic_shift a Ei Eo b Q.
Proof.
  intros; unfold atomic_shift.
  Intros P; Exists P; cancel.
  unfold ashift.
  apply andp_derives; auto.
  iIntros "H P"; iMod ("H" with "P") as (_) "[a H]".
  iDestruct "a" as (x) "a"; iExists x; iFrame.
  iIntros "!>"; iSplit.
  - iIntros "a"; iApply "H".
    iExists x; auto.
  - iIntros (y) "b"; iApply "H".
    simpl; iExists x; auto.
Qed.

End atomicity.

End atomics.

Hint Resolve empty_subseteq : core.

Definition atomic_spec_type W T := ProdType (ProdType W (ArrowType (ConstType T) Mpred)) (ConstType invG).

Definition super_non_expansive_a {A W} (a : forall ts : list Type, functors.MixVariantFunctor._functor
  (dependent_type_functor_rec ts W) (predicates_hered.pred rmap) -> A ts -> predicates_hered.pred rmap) :=
  forall n ts w x, approx n (a ts w x) =
  approx n (a ts (functors.MixVariantFunctor.fmap (dependent_type_functor_rec ts W) (approx n) (approx n) w) x).

Definition super_non_expansive_b {A B W} (b : forall ts : list Type, functors.MixVariantFunctor._functor
  (dependent_type_functor_rec ts W) (predicates_hered.pred rmap) -> A ts -> B ts -> predicates_hered.pred rmap) :=
  forall n ts w x y, approx n (b ts w x y) =
  approx n (b ts (functors.MixVariantFunctor.fmap (dependent_type_functor_rec ts W) (approx n) (approx n) w) x y).

Definition super_non_expansive_la {W} la := forall n ts w rho,
  Forall (fun l => approx n (!! locald_denote (l ts w) rho) = approx n (!! locald_denote (l ts
    (functors.MixVariantFunctor.fmap (dependent_type_functor_rec ts W) (approx n) (approx n) w)) rho)) la.

Definition super_non_expansive_lb {B W} lb := forall n ts w (v : B ts) rho,
  Forall (fun l => approx n (!! locald_denote (l ts w v) rho) = approx n (!! locald_denote (l ts
    (functors.MixVariantFunctor.fmap (dependent_type_functor_rec ts W) (approx n) (approx n) w) v) rho)) lb.

Import List.

(* A is the type of the abstract data. T is the type quantified over in the postcondition.
   W is the TypeTree of the witness for the rest of the function. *)
(*Notation atomic_spec1 T W args tz la P a t lb b Ei Eo :=
  (mk_funspec (pair args tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) '(w, Q, inv_names) =>
     PROP ()
     (LOCALx (map (fun l => l ts w) la)
     (SEP (atomic_shift(inv_names := inv_names) (a ts w) Ei Eo (b ts w) Q; P ts w))))
   (fun (ts: list Type) '(w, Q, inv_names) => EX v : T,
     PROP () (LOCALx (map (fun l => l ts w v) lb)
     (SEP (Q v)))) _ _).*)


Lemma atomic_spec_nonexpansive_pre' : forall {A T} {t : Inhabitant T} W P L R S2 Ei Eo SQ
  (HP : Forall (fun x => super_non_expansive (fun ts w _ => !! (x ts w))) P)
  (HL : Forall (fun x => super_non_expansive (fun ts w rho => !! (locald_denote (x ts w) rho))) L)
  (HR : Forall (fun x => super_non_expansive (fun ts w _ => x ts w)) R),
  super_non_expansive_a S2 ->
  super_non_expansive_b SQ ->
  @super_non_expansive (atomic_spec_type W T)
  (fun ts (_a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) =>
    let '(w, Q, inv_names) := _a in
    PROPx (map (fun P => P ts w) P) (LOCALx (map (fun L => L ts w) L)
     (SEPx (atomic_shift(A := A ts)(inv_names := inv_names) (S2 ts w) Ei Eo (SQ ts w) Q :: map (fun R => R ts w) R)))).
Proof.
  intros.
  replace _ with (fun ts (_a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) rho =>
    PROPx (map (fun P => P ts _a) (map (fun P ts _a => let '(w, _, _) := _a in P ts w) P)) (LOCALx (map (fun P => P ts _a) (map (fun P ts _a => let '(w, _, _) := _a in P ts w) L))
     (SEPx (map (fun R => R ts _a) ((fun ts _a => let '(w, Q, inv_names) := _a in atomic_shift(A := A ts)(inv_names := inv_names) (S2 ts w) Ei Eo (SQ ts w) Q) ::
        map (fun R ts _a => let '(w, _, _) := _a in R ts w) R)))) rho).
  apply PROP_LOCAL_SEP_super_non_expansive.
  - rewrite Forall_map.
    eapply Forall_impl, HP; simpl; intros.
    intros ?? ((?, ?), ?) ?; simpl; auto.
  - rewrite Forall_map.
    eapply Forall_impl, HL; simpl; intros.
    intros ?? ((?, ?), ?) ?; simpl; auto.
  - constructor.
    + intros ?? ((?, ?), ?) ?; simpl.
      rewrite -> atomic_shift_nonexpansive by auto; setoid_rewrite atomic_shift_nonexpansive at 2; auto.
      f_equal; f_equal; repeat extensionality; auto.
      rewrite approx_idem; auto.
    + rewrite Forall_map.
      eapply Forall_impl, HR; simpl; intros.
      intros ?? ((?, ?), ?) ?; simpl; auto.
  - extensionality ts x rho.
    destruct x as ((?, ?), ?).
    simpl; rewrite !map_map; reflexivity.
Qed.

Definition atomic_spec_type0 W := ProdType (ProdType W Mpred) (ConstType invG).

Lemma atomic_spec_nonexpansive_pre0 : forall {A} W P L R S2 Ei Eo SQ
  (HP : Forall (fun x => super_non_expansive (fun ts w _ => !! (x ts w))) P)
  (HL : Forall (fun x => super_non_expansive (fun ts w rho => !! (locald_denote (x ts w) rho))) L)
  (HR : Forall (fun x => super_non_expansive (fun ts w _ => x ts w)) R),
  super_non_expansive_a S2 ->
  super_non_expansive_b SQ ->
  @super_non_expansive (atomic_spec_type0 W)
  (fun ts (_a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) =>
    let '(w, Q, inv_names) := _a in
    PROPx (map (fun P => P ts w) P) (LOCALx (map (fun L => L ts w) L)
     (SEPx (atomic_shift(A := A ts)(B := unit)(inv_names := inv_names) (S2 ts w) Ei Eo (SQ ts w) (fun _ => Q) :: map (fun R => R ts w) R)))).
Proof.
  intros.
  replace _ with (fun ts (_a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) rho =>
    PROPx (map (fun P => P ts _a) (map (fun P ts _a => let '(w, _, _) := _a in P ts w) P)) (LOCALx (map (fun P => P ts _a) (map (fun P ts _a => let '(w, _, _) := _a in P ts w) L))
     (SEPx (map (fun R => R ts _a) ((fun ts _a => let '(w, Q, inv_names) := _a in atomic_shift(A := A ts)(inv_names := inv_names) (S2 ts w) Ei Eo (SQ ts w) (fun _ => Q)) ::
        map (fun R ts _a => let '(w, _, _) := _a in R ts w) R)))) rho).
  apply PROP_LOCAL_SEP_super_non_expansive.
  - rewrite Forall_map.
    eapply Forall_impl, HP; simpl; intros.
    intros ?? ((?, ?), ?) ?; simpl; auto.
  - rewrite Forall_map.
    eapply Forall_impl, HL; simpl; intros.
    intros ?? ((?, ?), ?) ?; simpl; auto.
  - constructor.
    + intros ?? ((?, ?), ?) ?; simpl.
      rewrite -> atomic_shift_nonexpansive; setoid_rewrite atomic_shift_nonexpansive at 2.
      f_equal; f_equal; repeat extensionality; auto.
      rewrite approx_idem; auto.
    + rewrite Forall_map.
      eapply Forall_impl, HR; simpl; intros.
      intros ?? ((?, ?), ?) ?; simpl; auto.
  - extensionality ts x rho.
    destruct x as ((?, ?), ?).
    simpl; rewrite !map_map; reflexivity.
Qed.

Lemma atomic_spec_nonexpansive_pre : forall {A T} {t : Inhabitant T} W P L R S2 Ei Eo SQ Pre
  (Heq : (forall ts (_a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG),
   Pre ts _a = let '(w, Q, inv_names) := _a in
    PROPx (map (fun P => P ts w) P) (LOCALx (map (fun L => L ts w) L)
     (SEPx (atomic_shift(A := A ts)(inv_names := inv_names) (S2 ts w) Ei Eo (SQ ts w) Q :: map (fun R => R ts w) R)))))
  (HP : Forall (fun x => super_non_expansive (fun ts w _ => !! (x ts w))) P)
  (HL : Forall (fun x => super_non_expansive (fun ts w rho => !! (locald_denote (x ts w) rho))) L)
  (HR : Forall (fun x => super_non_expansive (fun ts w _ => x ts w)) R),
  super_non_expansive_a S2 ->
  super_non_expansive_b SQ ->
  @super_non_expansive (atomic_spec_type W T) Pre.
Proof.
  intros.
  evar (Pre' : forall ts : list Type, functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG -> environ -> mpred).
  replace Pre with Pre'; subst Pre'; [apply (atomic_spec_nonexpansive_pre'(A := A)); eauto|].
  extensionality ts x; auto.
Qed.

Lemma atomic_spec_nonexpansive_post' : forall {T} W L R
  (HL : forall v, Forall (fun x => super_non_expansive (fun ts w rho => !! (locald_denote (x ts w v) rho))) L)
  (HR : forall v, Forall (fun x => super_non_expansive (fun ts w _ => x ts w)) (R v)),
  @super_non_expansive (atomic_spec_type W T)
  (fun ts (_a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) =>
    let '(w, Q, inv_names) := _a in
    EX v : T,
    PROP () (LOCALx (map (fun L => L ts w v) L) (SEPx (Q v :: map (fun R => R ts w) (R v))))).
Proof.
  intros.
  intros ?? ((w, Q), inv_names) ?; simpl.
  rewrite !approx_exp; f_equal; extensionality v.
  assert (@super_non_expansive (atomic_spec_type W T) (fun ts _a => let '(w, Q, inv_names) := _a in
    PROP () (LOCALx (map (fun L => L ts w v) L) (SEPx (Q v :: map (fun R => R ts w) (R v)))))); [|apply (H n ts (w, Q, inv_names))].
  replace _ with (fun ts (_a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) rho =>
    PROP () (LOCALx (map (fun P => P ts _a) (map (fun P ts _a => let '(w, _, _) := _a in P ts w v) L))
     (SEPx (map (fun P => P ts _a) ((fun ts _a => let '(_, Q, _) := _a in Q v) :: map (fun R ts _a => let '(w, _, _) := _a in R ts w) (R v))))) rho).
  apply (PROP_LOCAL_SEP_super_non_expansive (atomic_spec_type W T) []); auto.
  - rewrite Forall_map.
    eapply Forall_impl, HL; simpl; intros.
    intros ?? ((?, ?), ?) ?; simpl; auto.
  - repeat constructor.
    + intros ?? ((?, ?), ?) ?; simpl.
      rewrite approx_idem; auto.
    + rewrite Forall_map.
      eapply Forall_impl, HR; simpl; intros.
      intros ?? ((?, ?), ?) ?; simpl; auto.
  - extensionality ts' x rho'.
    destruct x as ((?, ?), ?).
    simpl; rewrite !map_map; reflexivity.
Qed.

Lemma atomic_spec_nonexpansive_post0 : forall W L R
  (HL : forall v, Forall (fun x => super_non_expansive (fun ts w rho => !! (locald_denote (x ts w v) rho))) L)
  (HR : Forall (fun x => super_non_expansive (fun ts w _ => x ts w)) R),
  @super_non_expansive (atomic_spec_type0 W)
  (fun ts (_a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) =>
    let '(w, Q, inv_names) := _a in
    PROP () (LOCALx (map (fun L => L ts w tt) L) (SEPx (Q :: map (fun R => R ts w) R)))).
Proof.
  intros.
  intros ?? ((w, Q), inv_names) ?; simpl.
  assert (@super_non_expansive (atomic_spec_type0 W) (fun ts _a => let '(w, Q, inv_names) := _a in
    PROP () (LOCALx (map (fun L => L ts w tt) L) (SEPx (Q :: map (fun R => R ts w) R))))); [|apply (H n ts (w, Q, inv_names))].
  replace _ with (fun ts (_a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) rho =>
    PROP () (LOCALx (map (fun P => P ts _a) (map (fun P ts _a => let '(w, _, _) := _a in P ts w tt) L))
     (SEPx (map (fun P => P ts _a) ((fun ts _a => let '(_, Q, _) := _a in Q) :: map (fun R ts _a => let '(w, _, _) := _a in R ts w) R)))) rho).
  apply (PROP_LOCAL_SEP_super_non_expansive (atomic_spec_type0 W) []); auto.
  - rewrite Forall_map.
    eapply Forall_impl, HL; simpl; intros.
    intros ?? ((?, ?), ?) ?; simpl; auto.
  - repeat constructor.
    + intros ?? ((?, ?), ?) ?; simpl.
      rewrite approx_idem; auto.
    + rewrite Forall_map.
      eapply Forall_impl, HR; simpl; intros.
      intros ?? ((?, ?), ?) ?; simpl; auto.
  - extensionality ts' x rho'.
    destruct x as ((?, ?), ?).
    simpl; rewrite !map_map; reflexivity.
Qed.

Lemma atomic_spec_nonexpansive_post : forall {T} W L R Post
  (Heq : (forall ts (_a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG),
  Post ts _a = let '(w, Q, inv_names) := _a in
    EX v : T,
    PROP () (LOCALx (map (fun L => L ts w v) L) (SEPx (Q v :: map (fun R => R ts w) (R v))))))
  (HL : forall v, Forall (fun x => super_non_expansive (fun ts w rho => !! (locald_denote (x ts w v) rho))) L)
  (HR : forall v, Forall (fun x => super_non_expansive (fun ts w _ => x ts w)) (R v)),
  @super_non_expansive (atomic_spec_type W T) Post.
Proof.
  intros.
  evar (Post' : forall ts : list Type, functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG -> environ -> mpred).
  replace Post with Post'; subst Post'; [apply atomic_spec_nonexpansive_post'; eauto|].
  extensionality ts x; auto.
Qed.

(* A is the type of the abstract data. T is the type quantified over in the postcondition.
   W is the TypeTree of the witness for the rest of the function. *)
Program Definition atomic_spec {A T} {t : Inhabitant T} W args tz la P Qp a lb b Ei Eo
  (Hla : super_non_expansive_la la) (HP : super_non_expansive' P) (HQp : forall v, super_non_expansive' (Qp v))
  (Ha : super_non_expansive_a(A := A) a) (Hlb : super_non_expansive_lb lb) (Hb : super_non_expansive_b b) :=
  mk_funspec (pair args tz) cc_default (atomic_spec_type W T)
  (fun (ts: list Type) '(w, Q, inv_names) =>
    PROP ()
    (LOCALx (map (fun l => l ts w) la)
    (SEP (atomic_shift(inv_names := inv_names) (a ts w) Ei Eo (b ts w) Q; P ts w))))
  (fun (ts: list Type) '(w, Q, inv_names) => EX v : T,
    PROP () (LOCALx (map (fun l => l ts w v) lb)
    (SEP (Q v; Qp v ts w)))) _ _.
Next Obligation.
Proof.
  intros; eapply atomic_spec_nonexpansive_pre with (P0 := [])(R := [_]); try assumption.
  { intros ? ((?, ?), ?); reflexivity. }
  all: auto.
  - rewrite Forall_forall; repeat intro.
    exploit Hla.
    rewrite Forall_forall; intro X; apply X; auto.
  - repeat constructor; repeat intro; auto.
Qed.
Next Obligation.
Proof.
  intros; eapply atomic_spec_nonexpansive_post with (R := fun v => [_]).
  { intros ? ((?, ?), ?); reflexivity. }
  - intros; rewrite Forall_forall; repeat intro.
    exploit Hlb.
    rewrite Forall_forall; intro X; apply X; auto.
  - repeat constructor.
    unfold super_non_expansive, super_non_expansive' in *.
    intros; apply HQp.
Qed.

Definition stable_spec_type W := ProdType (ProdType (ProdType W
  (ArrowType (DependentType 0) (ArrowType (DependentType 1) Mpred))) (ArrowType (DependentType 1) Mpred)) (ConstType invG).

(*Lemma stabilize : forall T W args tz P1 P2 Q1 Q2 neP1 neP2 neQ1 neQ2
  PP la P a lb b Ei Eo Q'
  (Hpre1 : forall ts w Q inv_names, P1 ts (w, Q, inv_names) =
     PROP (PP ts w)
     (LOCALx (map (fun l => l ts w) la)
     (SEP (atomic_shift(inv_names := inv_names) (a ts w) Ei Eo (b ts w) Q; P ts w))))
  (Hpost1 : forall ts w Q inv_names, Q1 ts (w, Q, inv_names) =
     EX v : T, PROP () (LOCALx (map (fun l => l ts w v) lb) (SEP (Q v))))
  (Hpre2 : forall ts w b' Q inv_names, P2 ts (w, b', Q, inv_names) =
     PROP (PP ts w)
     (LOCALx (map (fun l => l ts w) la)
     (SEP (atomic_shift(inv_names := inv_names) (a ts w) Ei Eo b' Q; P ts w))))
  (Hpost2 : forall ts w b' Q inv_names, Q2 ts (w, b', Q, inv_names) =
    EX v1 : _, EX v2 : _,
     PROP () (LOCALx (map (fun l => l ts w v2) lb)
     (SEP (atomic_shift(inv_names := inv_names) (a ts w) Ei Eo b' Q; Q' ts w v1 v2))))
  (Hb : forall ts w v1 v2, b ts w v1 v2 |-- a ts w v1 * Q' ts w v1 v2),
  funspec_sub (mk_funspec (pair args tz) cc_default (atomic_spec_type W T) P1 Q1 neP1 neQ1)
    (mk_funspec (pair args tz) cc_default (stable_spec_type W) P2 Q2 neP2 neQ2).
Proof.
  intros; apply subsume_subsume.
  unfold funspec_sub'; repeat (split; auto); intros.
  destruct x2 as (((w, b'), Q), inv_names).
  simpl funsig_of_funspec.
  rewrite Hpre2.
  set (AS := atomic_shift _ _ _ _ _).
  eapply derives_trans, ghost_seplog.bupd_intro.
  Exists ts2 (w, (fun v2 => AS * EX v1 : _, Q' ts2 w v1 v2), inv_names) emp.
  simpl in *; intro.
  unfold liftx; simpl.
  unfold lift.
  rewrite emp_sepcon.
  apply andp_right.
  - apply andp_left2.
    rewrite Hpre1.
    unfold PROPx, LOCALx, SEPx; simpl.
    do 2 (apply andp_derives; auto).
    unfold AS, atomic_shift; Intros P'; Exists P'; cancel.
    sep_apply cored_dup_cored.
    apply andp_derives; auto.
    iIntros "[H AS] P"; iMod ("H" with "P") as (v1) "[a H]".
    iExists v1; iFrame.
    iIntros "!>"; iSplit.
    + iIntros "a".
      iDestruct "AS" as "[_ e]"; iMod (cored_emp with "e") as "_".
      iApply "H"; auto.
    + iIntros (y) "b".
      iDestruct (Hb with "b") as "[a Q]".
      iMod ("H" with "a").
      iIntros "!>"; iSplitR "Q".
      * iExists P'; iFrame.
      * iExists v1; auto.
  - apply prop_right; intros.
    apply andp_left2; rewrite emp_sepcon; auto.
    rewrite Hpost1 Hpost2.
    unfold PROPx, LOCALx, SEPx; simpl.
    eapply derives_trans, ghost_seplog.bupd_intro.
    Intros v2 v1; Exists v1 v2; rewrite sepcon_assoc; unfold AS; auto.
Qed.

Lemma stabilize0 : forall W args tz P1 P2 Q1 Q2 neP1 neP2 neQ1 neQ2
  PP la P a lb b Ei Eo Q'
  (Hpre1 : forall ts w Q inv_names, P1 ts (w, Q, inv_names) =
    PROP (PP ts w)
     (LOCALx (map (fun l => l ts w) la)
     (SEP (atomic_shift(B := unit)(inv_names := inv_names) (a ts w) Ei Eo (b ts w) (fun _ => Q); P ts w))))
  (Hpost1 : forall ts w Q inv_names, Q1 ts (w, Q, inv_names) =
     PROP () (LOCALx (map (fun l => l ts w) lb) ((SEPx (Q :: cons SPx%logic .. (cons SPy%logic nil) ..)))))
  (Hpre2 : forall ts w b' Q inv_names, P2 ts (w, b', Q, inv_names) =
     PROP (PP ts w)
     (LOCALx (map (fun l => l ts w) la)
     (SEP (atomic_shift(inv_names := inv_names) (a ts w) Ei Eo b' Q; P ts w))))
  (Hpost2 : forall ts w b' Q inv_names, Q2 ts (w, b', Q, inv_names) =
    EX v1 : _,
     PROP () (LOCALx (map (fun l => l ts w) lb)
     (SEP (atomic_shift(inv_names := inv_names) (a ts w) Ei Eo b' Q; Q' ts w v1))))
  (Hb : forall ts w v1, b ts w v1 tt |-- a ts w v1 * Q' ts w v1),
  funspec_sub (mk_funspec (pair args tz) cc_default (atomic_spec_type0 W) P1 Q1 neP1 neQ1)
    (mk_funspec (pair args tz) cc_default (stable_spec_type W) P2 Q2 neP2 neQ2).
Proof.
  intros; apply subsume_subsume.
  unfold funspec_sub'; repeat (split; auto); intros.
  destruct x2 as (((w, b'), Q), inv_names).
  simpl funsig_of_funspec.
  rewrite Hpre2.
  set (AS := atomic_shift _ _ _ _ _).
  eapply derives_trans, ghost_seplog.bupd_intro.
  Exists ts2 (w, (AS * EX v1 : _, Q' ts2 w v1), inv_names) emp.
  simpl in *; intro.
  unfold liftx; simpl.
  unfold lift.
  rewrite emp_sepcon.
  apply andp_right.
  - apply andp_left2.
    rewrite Hpre1.
    unfold PROPx, LOCALx, SEPx; simpl.
    do 2 (apply andp_derives; auto).
    unfold AS, atomic_shift; Intros P'; Exists P'; cancel.
    sep_apply cored_dup_cored.
    apply andp_derives; auto.
    iIntros "[H AS] P"; iMod ("H" with "P") as (v1) "[a H]".
    iExists v1; iFrame.
    iIntros "!>"; iSplit.
    + iIntros "a".
      iDestruct "AS" as "[_ e]"; iMod (cored_emp with "e") as "_".
      iApply "H"; auto.
    + iIntros ([]) "b".
      iDestruct (Hb with "b") as "[a Q]".
      iMod ("H" with "a").
      iIntros "!>"; iSplitR "Q".
      * iExists P'; iFrame.
      * iExists v1; auto.
  - apply prop_right; intros.
    apply andp_left2; rewrite emp_sepcon; auto.
    rewrite Hpost1 Hpost2.
    unfold PROPx, LOCALx, SEPx; simpl.
    eapply derives_trans, ghost_seplog.bupd_intro.
    Intros v1; Exists v1; rewrite sepcon_assoc; unfold AS; auto.
Qed.*)


Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '(x1, Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '(x1, Q, inv_names) := __a in
    EX r : T,
     PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) (SEPx (Q r :: cons SPx .. (cons SPy nil) ..))))
   (@atomic_spec_nonexpansive_pre' _ T _ W (cons (fun ts __a => let x1 := __a in Px%type) .. (cons (fun ts __a => let x1 := __a in Py%type) nil) ..)
      (cons (fun ts __a => let x1 := __a in Lx%type) .. (cons (fun ts __a => let x1 := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let x1 := __a in S1x%logic) .. (cons (fun ts __a => let x1 := __a in S1y%logic) nil) ..)
      (fun ts __a x => let x1 := __a in S2) Ei Eo
     (fun ts __a x r => let x1 := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post' W (cons (fun ts __a r => let x1 := __a in LQx%logic) .. (cons (fun ts __a r => let x1 := __a in LQy%logic) nil) ..)
      (fun r => cons (fun ts __a => let x1 := __a in SPx%logic) .. (cons (fun ts __a => let x1 := __a in SPy%logic) nil) ..) _ _))
  (at level 200, x at level 0, Ei at level 0, Eo at level 0, x1 at level 0,
        S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '(x1, Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '(x1, Q, inv_names) := __a in
    EX r : T,
     PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) (SEPx (Q r :: cons SPx .. (cons SPy nil) ..))))
   (@atomic_spec_nonexpansive_pre' _ T _ W (cons (fun ts __a => let x1 := __a in Px%type) .. (cons (fun ts __a => let x1 := __a in Py%type) nil) ..)
      (cons (fun ts __a => let x1 := __a in Lx%type) .. (cons (fun ts __a => let x1 := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let x1 := __a in S1x%logic) .. (cons (fun ts __a => let x1 := __a in S1y%logic) nil) ..)
      (fun ts __a x => let x1 := __a in S2) Ei Eo
     (fun ts __a x r => let x1 := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post' W (cons (fun ts __a r => let x1 := __a in LQx%logic) .. (cons (fun ts __a r => let x1 := __a in LQy%logic) nil) ..)
      (fun r => cons (fun ts __a => let x1 := __a in SPx%logic) .. (cons (fun ts __a => let x1 := __a in SPy%logic) nil) ..) _ _))
  (at level 200, x at level 0, Ei at level 0, Eo at level 0, x1 at level 0,
             S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type0 W)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '(x1, Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) (fun _ => Q)) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '(x1, Q, inv_names) := __a in
     PROP () (LOCALx (cons LQx%logic .. (cons LQy%logic nil) ..) (SEPx (Q :: cons SPx%logic .. (cons SPy%logic nil) ..))))
   (@atomic_spec_nonexpansive_pre0 _ W (cons (fun ts __a => let x1 := __a in Px%type) .. (cons (fun ts __a => let x1 := __a in Py%type) nil) ..)
      (cons (fun ts __a => let x1 := __a in Lx%type) .. (cons (fun ts __a => let x1 := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let x1 := __a in S1x%logic) .. (cons (fun ts __a => let x1 := __a in S1y%logic) nil) ..)
      (fun ts __a x => let x1 := __a in S2) Ei Eo
     (fun ts __a x _ => let x1 := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post0 W (cons (fun ts __a _ => let x1 := __a in LQx%logic) .. (cons (fun ts __a _ => let x1 := __a in LQy%logic) nil) ..)
      (cons (fun ts __a => let x1 := __a in SPx%logic) .. (cons (fun ts __a => let x1 := __a in SPy%logic) nil) ..) _ _))
  (at level 200, x at level 0, Ei at level 0, Eo at level 0, x1 at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '(x1, Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '(x1, Q, inv_names) := __a in
    EX r : T,
     PROP () LOCAL () (SEPx (Q r :: cons SPx .. (cons SPy nil) ..)))
   (@atomic_spec_nonexpansive_pre' _ T _ W (cons (fun ts __a => let x1 := __a in Px%type) .. (cons (fun ts __a => let x1 := __a in Py%type) nil) ..)
      (cons (fun ts __a => let x1 := __a in Lx%type) .. (cons (fun ts __a => let x1 := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let x1 := __a in S1x%logic) .. (cons (fun ts __a => let x1 := __a in S1y%logic) nil) ..)
      (fun ts __a x => let x1 := __a in S2) Ei Eo
     (fun ts __a x r => let x1 := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post' W [] (fun r => cons (fun ts __a => let x1 := __a in SPx%logic) .. (cons (fun ts __a => let x1 := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0, x1 at level 0,
             S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type0 W)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '(x1, Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(B := unit)(inv_names := inv_names) (fun x => S2) Ei Eo (fun x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) (fun _ => Q)) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '(x1, Q, inv_names) := __a in
     PROP () LOCAL () (SEPx (Q :: cons SPx%logic .. (cons SPy%logic nil) ..)))
   (@atomic_spec_nonexpansive_pre0 _ W (cons (fun ts __a => let x1 := __a in Px%type) .. (cons (fun ts __a => let x1 := __a in Py%type) nil) ..)
      (cons (fun ts __a => let x1 := __a in Lx%type) .. (cons (fun ts __a => let x1 := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let x1 := __a in S1x%logic) .. (cons (fun ts __a => let x1 := __a in S1y%logic) nil) ..)
      (fun ts __a x => let x1 := __a in S2) Ei Eo
     (fun ts __a x _ => let x1 := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post0 W [] (cons (fun ts __a => let x1 := __a in SPx%logic) .. (cons (fun ts __a => let x1 := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )  " :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type0 W)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '(x1, Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) (fun _ => Q)) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '(x1, Q, inv_names) := __a in
     PROP () LOCAL () (SEPx (Q :: cons SPx%logic .. (cons SPy%logic nil) ..)))
   (@atomic_spec_nonexpansive_pre0 _ W (cons (fun ts __a => let x1 := __a in Px%type) .. (cons (fun ts __a => let x1 := __a in Py%type) nil) ..)
      (cons (fun ts __a => let x1 := __a in Lx%type) .. (cons (fun ts __a => let x1 := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let x1 := __a in S1x%logic) .. (cons (fun ts __a => let x1 := __a in S1y%logic) nil) ..)
      (fun ts __a x => let x1 := __a in S2) Ei Eo
     (fun ts __a x _ => let x1 := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post0 W [] (cons (fun ts __a => let x1 := __a in SPx%logic) .. (cons (fun ts __a => let x1 := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0, x1 at level 0,
       S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 'PRE'  [ ] 'PROP' () 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type0 W)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '(x1, Q, inv_names) := __a in
     PROPx nil
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) (fun _ => Q)) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '(x1, Q, inv_names) := __a in
     PROP () LOCAL () (SEPx (Q :: cons SPx%logic .. (cons SPy%logic nil) ..)))
   (@atomic_spec_nonexpansive_pre0 _ W nil
      (cons (fun ts __a => let x1 := __a in Lx%type) .. (cons (fun ts __a => let x1 := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let x1 := __a in S1x%logic) .. (cons (fun ts __a => let x1 := __a in S1y%logic) nil) ..)
      (fun ts __a x => let x1 := __a in S2) Ei Eo
     (fun ts __a x _ => let x1 := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post0 W [] (cons (fun ts __a => let x1 := __a in SPx%logic) .. (cons (fun ts __a => let x1 := __a in SPy%logic) nil) ..) _ _))
  (at level 200, x at level 0, Ei at level 0, Eo at level 0, x1 at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'NO_OBJ' 'INVS' Ei Eo 'WITH' x1 : t1 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '(x1, Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(A := unit)(inv_names := inv_names) (fun _ => S2) Ei Eo (fun _ r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '(x1, Q, inv_names) := __a in
    EX r : T,
     PROP () LOCAL () (SEPx (Q r :: cons SPx .. (cons SPy nil) ..)))
   (@atomic_spec_nonexpansive_pre' _ T _ W (cons (fun ts __a => let x1 := __a in Px%type) .. (cons (fun ts __a => let x1 := __a in Py%type) nil) ..)
      (cons (fun ts __a => let x1 := __a in Lx%type) .. (cons (fun ts __a => let x1 := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let x1 := __a in S1x%logic) .. (cons (fun ts __a => let x1 := __a in S1y%logic) nil) ..)
      (fun ts __a _ => let x1 := __a in S2) Ei Eo
     (fun ts __a _ r => let x1 := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post' W [] (fun r => cons (fun ts __a => let x1 := __a in SPx%logic) .. (cons (fun ts __a => let x1 := __a in SPy%logic) nil) ..) _ _)) (at level 200, Ei at level 0, Eo at level 0, x1 at level 0,
             S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'NO_OBJ' 'INVS' Ei Eo 'WITH' x1 : t1 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type0 W)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '(x1, Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(A := unit)(inv_names := inv_names) (fun _ => S2) Ei Eo (fun _ _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) (fun _ => Q)) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '(x1, Q, inv_names) := __a in
     PROP () LOCAL () (SEPx (Q :: cons SPx%logic .. (cons SPy%logic nil) ..)))
   (@atomic_spec_nonexpansive_pre0 _ W (cons (fun ts __a => let x1 := __a in Px%type) .. (cons (fun ts __a => let x1 := __a in Py%type) nil) ..)
      (cons (fun ts __a => let x1 := __a in Lx%type) .. (cons (fun ts __a => let x1 := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let x1 := __a in S1x%logic) .. (cons (fun ts __a => let x1 := __a in S1y%logic) nil) ..)
      (fun ts __a _ => let x1 := __a in S2) Ei Eo
     (fun ts __a _ _ => let x1 := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post0 W [] (cons (fun ts __a => let x1 := __a in SPx%logic) .. (cons (fun ts __a => let x1 := __a in SPy%logic) nil) ..) _ _)) (at level 200, Ei at level 0, Eo at level 0, x1 at level 0,
        S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '(x1, Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '(x1, Q, inv_names) := __a in
    EX r : T,
     PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) ((SEPx (Q r :: cons SPx .. (cons SPy nil) ..)))))
   (@atomic_spec_nonexpansive_pre' _ T _ W (cons (fun ts __a => let x1 := __a in Px%type) .. (cons (fun ts __a => let x1 := __a in Py%type) nil) ..)
      (cons (fun ts __a => let x1 := __a in Lx%type) .. (cons (fun ts __a => let x1 := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let x1 := __a in S1x%logic) .. (cons (fun ts __a => let x1 := __a in S1y%logic) nil) ..)
      (fun ts __a x => let x1 := __a in S2) Ei Eo
     (fun ts __a x r => let x1 := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post' W (cons (fun ts __a r => let x1 := __a in LQx%logic) .. (cons (fun ts __a r => let x1 := __a in LQy%logic) nil) ..)
     (fun r => cons (fun ts __a => let x1 := __a in SPx%logic) .. (cons (fun ts __a => let x1 := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type0 W)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '(x1, Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) (fun _ => Q)) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '(x1, Q, inv_names) := __a in
     PROP () (LOCALx (cons LQx%logic .. (cons LQy%logic nil) ..) ((SEPx (Q :: cons SPx%logic .. (cons SPy%logic nil) ..)))))
   (@atomic_spec_nonexpansive_pre0 _ W (cons (fun ts __a => let x1 := __a in Px%type) .. (cons (fun ts __a => let x1 := __a in Py%type) nil) ..)
      (cons (fun ts __a => let x1 := __a in Lx%type) .. (cons (fun ts __a => let x1 := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let x1 := __a in S1x%logic) .. (cons (fun ts __a => let x1 := __a in S1y%logic) nil) ..)
      (fun ts __a x => let x1 := __a in S2) Ei Eo
     (fun ts __a x _ => let x1 := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post0 W (cons (fun ts __a _ => let x1 := __a in LQx%logic) .. (cons (fun ts __a _ => let x1 := __a in LQy%logic) nil) ..)
      (cons (fun ts __a => let x1 := __a in SPx%logic) .. (cons (fun ts __a => let x1 := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2), Q, inv_names) := __a in
    EX r : T,
     PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) ((SEPx (Q r :: cons SPx .. (cons SPy nil) ..)))))
   (@atomic_spec_nonexpansive_pre' _ T _ W (cons (fun ts __a => let '(x1, x2) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2) := __a in S2) Ei Eo
     (fun ts __a x r => let '(x1, x2) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post' W (cons (fun ts __a r => let '(x1, x2) := __a in LQx%logic) .. (cons (fun ts __a r => let '(x1, x2) := __a in LQy%logic) nil) ..)
      (fun r => cons (fun ts __a => let '(x1, x2) := __a in SPx%logic) .. (cons (fun ts __a => let '(x1, x2) := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, x2 at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 'PRE'  [ ] 'PROP' () 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type0 W)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts W) mpred * mpred * invG) => let '((x1, x2), Q, inv_names) := __a in
     PROPx nil
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(B := unit)(inv_names := inv_names) (fun x => S2) Ei Eo (fun x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) (fun _ => Q)) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts W) mpred * mpred * invG) => let '((x1, x2), Q, inv_names) := __a in
     PROP () (LOCALx nil ((SEPx (Q :: cons SPx%logic .. (cons SPy%logic nil) ..)))))
   (@atomic_spec_nonexpansive_pre0 _ W nil
      (cons (fun ts __a => let '(x1, x2) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2) := __a in S2) Ei Eo
     (fun ts __a x _ => let '(x1, x2) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post0 W nil (cons (fun ts __a => let '(x1, x2) := __a in SPx%logic) .. (cons (fun ts __a => let '(x1, x2) := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, x2 at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 'PRE'  [ ] 'PROP' () 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2), Q, inv_names) := __a in
     PROPx nil
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2), Q, inv_names) := __a in
    EX r : T,
     PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) ((SEPx (Q r :: cons SPx .. (cons SPy nil) ..)))))
   (@atomic_spec_nonexpansive_pre' _ T _ W nil
      (cons (fun ts __a => let '(x1, x2) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2) := __a in S2) Ei Eo
     (fun ts __a x r => let '(x1, x2) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post' W (cons (fun ts __a r => let x1 := __a in LQx%logic) .. (cons (fun ts __a r => let x1 := __a in LQy%logic) nil) ..)
      (fun r => cons (fun ts __a => let '(x1, x2) := __a in SPx%logic) .. (cons (fun ts __a => let '(x1, x2) := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, x2 at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 'PRE'  [ ] 'PROP' () 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type0 W)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '((x1, x2), Q, inv_names) := __a in
     PROPx nil
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(B := unit)(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) (fun _ => Q)) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '((x1, x2), Q, inv_names) := __a in
     PROP () (LOCALx nil ((SEPx (Q :: cons SPx%logic .. (cons SPy%logic nil) ..)))))
   (@atomic_spec_nonexpansive_pre0 _ W nil
      (cons (fun ts __a => let '(x1, x2) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2) := __a in S2) Ei Eo
     (fun ts __a x r => let '(x1, x2) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post0 W nil (cons (fun ts __a => let '(x1, x2) := __a in SPx%logic) .. (cons (fun ts __a => let '(x1, x2) := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, x2 at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3), Q, inv_names) := __a in
    EX r : T,
     PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) ((SEPx (Q r :: cons SPx .. (cons SPy nil) ..)))))
   (@atomic_spec_nonexpansive_pre' _ T _ W (cons (fun ts __a => let '(x1, x2, x3) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3) := __a in S2) Ei Eo
     (fun ts __a x r => let '(x1, x2, x3) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post' W (cons (fun ts __a r => let '(x1, x2, x3) := __a in LQx%logic) .. (cons (fun ts __a r => let '(x1, x2, x3) := __a in LQy%logic) nil) ..)
      (fun r => cons (fun ts __a => let '(x1, x2, x3) := __a in SPx%logic) .. (cons (fun ts __a => let '(x1, x2, x3) := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3), Q, inv_names) := __a in
    EX r : T,
     PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) ((SEPx (Q r :: cons SPx .. (cons SPy nil) ..)))))
   (@atomic_spec_nonexpansive_pre' _ T _ W (cons (fun ts __a => let '(x1, x2, x3) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3) := __a in S2) Ei Eo
     (fun ts __a x r => let '(x1, x2, x3) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post' W (cons (fun ts __a r => let '(x1, x2, x3) := __a in LQx%logic) .. (cons (fun ts __a r => let '(x1, x2, x3) := __a in LQy%logic) nil) ..)
      (fun r => cons (fun ts __a => let '(x1, x2, x3) := __a in SPx%logic) .. (cons (fun ts __a => let '(x1, x2, x3) := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type0 W)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '((x1, x2, x3), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(B := unit)(inv_names := inv_names) (fun x => S2) Ei Eo (fun x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) (fun _ => Q)) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '((x1, x2, x3), Q, inv_names) := __a in
     PROP () (LOCALx nil ((SEPx (Q :: cons SPx%logic .. (cons SPy%logic nil) ..)))))
   (@atomic_spec_nonexpansive_pre0 _ W (cons (fun ts __a => let '(x1, x2, x3) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3) := __a in S2) Ei Eo
     (fun ts __a x _ => let '(x1, x2, x3) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post0 W nil (cons (fun ts __a => let '(x1, x2, x3) := __a in SPx%logic) .. (cons (fun ts __a => let '(x1, x2, x3) := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 'PRE'  [ ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type0 W)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '((x1, x2, x3), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(B := unit)(inv_names := inv_names) (fun x => S2) Ei Eo (fun x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) (fun _ => Q)) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '((x1, x2, x3), Q, inv_names) := __a in
     PROP () (LOCALx nil ((SEPx (Q :: cons SPx%logic .. (cons SPy%logic nil) ..)))))
   (@atomic_spec_nonexpansive_pre0 _ W (cons (fun ts __a => let '(x1, x2, x3) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3) := __a in S2) Ei Eo
     (fun ts __a x _ => let '(x1, x2, x3) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post0 W nil (cons (fun ts __a => let '(x1, x2, x3) := __a in SPx%logic) .. (cons (fun ts __a => let '(x1, x2, x3) := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 'PRE'  [ ] 'PROP' () 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair nil tz) cc_default (atomic_spec_type0 W)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '((x1, x2, x3), Q, inv_names) := __a in
     PROP ()
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(B := unit)(inv_names := inv_names) (fun x => S2) Ei Eo (fun x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) (fun _ => Q)) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '((x1, x2, x3), Q, inv_names) := __a in
     PROP () (LOCALx nil ((SEPx (Q :: cons SPx%logic .. (cons SPy%logic nil) ..)))))
   (@atomic_spec_nonexpansive_pre0 _ W nil
      (cons (fun ts __a => let '(x1, x2, x3) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3) := __a in S2) Ei Eo
     (fun ts __a x _ => let '(x1, x2, x3) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post0 W nil (cons (fun ts __a => let '(x1, x2, x3) := __a in SPx%logic) .. (cons (fun ts __a => let '(x1, x2, x3) := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4), Q, inv_names) := __a in
    EX r : T,
     PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) ((SEPx (Q r :: cons SPx .. (cons SPy nil) ..)))))
   (@atomic_spec_nonexpansive_pre' _ T _ W (cons (fun ts __a => let '(x1, x2, x3, x4) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3, x4) := __a in S2) Ei Eo
     (fun ts __a x r => let '(x1, x2, x3, x4) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post' W (cons (fun ts __a r => let '(x1, x2, x3, x4) := __a in LQx%logic) .. (cons (fun ts __a r => let '(x1, x2, x3, x4) := __a in LQy%logic) nil) ..)
      (fun r => cons (fun ts __a => let '(x1, x2, x3, x4) := __a in SPx%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4) := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type0 W)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '((x1, x2, x3, x4), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(B := unit)(inv_names := inv_names) (fun x => S2) Ei Eo (fun x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) (fun _ => Q)) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '((x1, x2, x3, x4), Q, inv_names) := __a in
     PROP () (LOCALx nil ((SEPx (Q :: cons SPx%logic .. (cons SPy%logic nil) ..)))))
   (@atomic_spec_nonexpansive_pre0 _ W (cons (fun ts __a => let '(x1, x2, x3, x4) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3, x4) := __a in S2) Ei Eo
     (fun ts __a x r => let '(x1, x2, x3, x4) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post0 W nil (cons (fun ts __a => let '(x1, x2, x3, x4) := __a in SPx%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4) := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5), Q, inv_names) := __a in
    EX r : T,
     PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) ((SEPx (Q r :: cons SPx .. (cons SPy nil) ..)))))
   (@atomic_spec_nonexpansive_pre' _ T _ W (cons (fun ts __a => let '(x1, x2, x3, x4, x5) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3, x4, x5) := __a in S2) Ei Eo
     (fun ts __a x r => let '(x1, x2, x3, x4, x5) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post' W (cons (fun ts __a r => let '(x1, x2, x3, x4, x5) := __a in LQx%logic) .. (cons (fun ts __a r => let '(x1, x2, x3, x4, x5) := __a in LQy%logic) nil) ..)
      (fun r => cons (fun ts __a => let '(x1, x2, x3, x4, x5) := __a in SPx%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5) := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type0 W)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '((x1, x2, x3, x4, x5), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(B := unit)(inv_names := inv_names) (fun x => S2) Ei Eo (fun x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) (fun _ => Q)) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '((x1, x2, x3, x4, x5), Q, inv_names) := __a in
     PROP () (LOCALx nil ((SEPx (Q :: cons SPx%logic .. (cons SPy%logic nil) ..)))))
   (@atomic_spec_nonexpansive_pre0 _ W (cons (fun ts __a => let '(x1, x2, x3, x4, x5) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3, x4, x5) := __a in S2) Ei Eo
     (fun ts __a x r => let '(x1, x2, x3, x4, x5) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post0 W nil (cons (fun ts __a => let '(x1, x2, x3, x4, x5) := __a in SPx%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5) := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6), Q, inv_names) := __a in
    EX r : T,
     PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) ((SEPx (Q r :: cons SPx .. (cons SPy nil) ..)))))
   (@atomic_spec_nonexpansive_pre' _ T _ W (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3, x4, x5, x6) := __a in S2) Ei Eo
     (fun ts __a x r => let '(x1, x2, x3, x4, x5, x6) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post' W (cons (fun ts __a r => let '(x1, x2, x3, x4, x5, x6) := __a in LQx%logic) .. (cons (fun ts __a r => let '(x1, x2, x3, x4, x5, x6) := __a in LQy%logic) nil) ..)
      (fun r => cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in SPx%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, x6 at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6), Q, inv_names) := __a in
    EX r : T,
     PROP () LOCAL () ((SEPx (Q r :: cons SPx .. (cons SPy nil) ..))))
   (@atomic_spec_nonexpansive_pre' _ T _ W (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3, x4, x5, x6) := __a in S2) Ei Eo
     (fun ts __a x r => let '(x1, x2, x3, x4, x5, x6) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post' W nil (fun r => cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in SPx%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, x6 at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type0 W)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '((x1, x2, x3, x4, x5, x6), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names)(B := unit) (fun x => S2) Ei Eo (fun x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) (fun _ => Q)) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '((x1, x2, x3, x4, x5, x6), Q, inv_names) := __a in
     PROP () LOCAL () ((SEPx (Q :: cons SPx%logic .. (cons SPy%logic nil) ..))))
   (@atomic_spec_nonexpansive_pre0 _ W (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3, x4, x5, x6) := __a in S2) Ei Eo
     (fun ts __a x _ => let '(x1, x2, x3, x4, x5, x6) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post0 W nil (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in SPx%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6) := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, x6 at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6, x7), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6, x7), Q, inv_names) := __a in
    EX r : T,
     PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) ((SEPx (Q r :: cons SPx .. (cons SPy nil) ..)))))
   (@atomic_spec_nonexpansive_pre' _ T _ W (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3, x4, x5, x6, x7) := __a in S2) Ei Eo
     (fun ts __a x r => let '(x1, x2, x3, x4, x5, x6, x7) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post' W (cons (fun ts __a r => let '(x1, x2, x3, x4, x5, x6, x7) := __a in LQx%logic) .. (cons (fun ts __a r => let '(x1, x2, x3, x4, x5, x6, x7) := __a in LQy%logic) nil) ..)
      (fun r => cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in SPx%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, x6 at level 0, x7 at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6, x7), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6, x7), Q, inv_names) := __a in
    EX r : T,
     PROP () LOCAL () ((SEPx (Q r :: cons SPx .. (cons SPy nil) ..))))
   (@atomic_spec_nonexpansive_pre' _ T _ W (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3, x4, x5, x6, x7) := __a in S2) Ei Eo
     (fun ts __a x r => let '(x1, x2, x3, x4, x5, x6, x7) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post' W nil (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in SPx%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, x6 at level 0, x7 at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type0 W)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '((x1, x2, x3, x4, x5, x6, x7), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(B := unit)(inv_names := inv_names) (fun x => S2) Ei Eo (fun x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '((x1, x2, x3, x4, x5, x6, x7), Q, inv_names) := __a in
     PROP () (LOCALx (cons LQx%logic .. (cons LQy%logic nil) ..) ((SEPx (Q :: cons SPx%logic .. (cons SPy%logic nil) ..)))))
   (@atomic_spec_nonexpansive_pre0 _ W (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3, x4, x5, x6, x7) := __a in S2) Ei Eo
     (fun ts __a x _ => let '(x1, x2, x3, x4, x5, x6, x7) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post0 W (cons (fun ts __a _ => let '(x1, x2, x3, x4, x5, x6, x7) := __a in LQx%logic) .. (cons (fun ts __a _ => let '(x1, x2, x3, x4, x5, x6, x7) := __a in LQy%logic) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in SPx%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, x6 at level 0, x7 at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type0 W)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '((x1, x2, x3, x4, x5, x6, x7), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(B := unit)(inv_names := inv_names) (fun x => S2) Ei Eo (fun x _ => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) (fun _ => Q)) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * mpred * invG) => let '((x1, x2, x3, x4, x5, x6, x7), Q, inv_names) := __a in
     PROP () LOCAL () ((SEPx (Q :: cons SPx%logic .. (cons SPy%logic nil) ..))))
   (@atomic_spec_nonexpansive_pre0 _ W (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3, x4, x5, x6, x7) := __a in S2) Ei Eo
     (fun ts __a x _ => let '(x1, x2, x3, x4, x5, x6, x7) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post0 W nil (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in SPx%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7) := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, x6 at level 0, x7 at level 0, S2 at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6, x7, x8), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6, x7, x8), Q, inv_names) := __a in
    EX r : T,
     PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) ((SEPx (Q r :: cons SPx .. (cons SPy nil) ..)))))
   (@atomic_spec_nonexpansive_pre' _ T _ W (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in S2) Ei Eo
     (fun ts __a x r => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post' W (cons (fun ts __a r => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in LQx%logic) .. (cons (fun ts __a r => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in LQy%logic) nil) ..)
      (fun r => cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in SPx%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6, x7, x8), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6, x7, x8), Q, inv_names) := __a in
    EX r : T,
     PROP () LOCAL () ((SEPx (Q r :: cons SPx .. (cons SPy nil) ..))))
   (@atomic_spec_nonexpansive_pre' _ T _ W (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in S2) Ei Eo
     (fun ts __a x r => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post' W nil (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in SPx%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8) := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0,
             S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' ( LQx ; .. ; LQy ) 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6, x7, x8, x9), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6, x7, x8, x9), Q, inv_names) := __a in
    EX r : T,
     PROP () (LOCALx (cons LQx .. (cons LQy nil) ..) ((SEPx (Q r :: cons SPx .. (cons SPy nil) ..)))))
   (@atomic_spec_nonexpansive_pre' _ T _ W (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in S2) Ei Eo
     (fun ts __a x r => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post' W (cons (fun ts __a r => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in LQx%logic) .. (cons (fun ts __a r => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in LQy%logic) nil) ..)
      (fun r => cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in SPx%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             S2 at level 0, r at level 0, T at level 0).

Notation "'ATOMIC' 'TYPE' W 'OBJ' x 'INVS' Ei Eo 'WITH' x1 : t1 , x2 : t2 , x3 : t3 , x4 : t4 , x5 : t5 , x6 : t6 , x7 : t7 , x8 : t8 , x9 : t9 'PRE'  [ u , .. , v ] 'PROP' ( Px ; .. ; Py ) 'LOCAL' ( Lx ; .. ; Ly ) 'SEP' ( S1x ; .. ; S1y ) '|' S2 'POST' [ tz ] 'EX' r : T , 'PROP' () 'LOCAL' () 'SEP' ( SPx ; .. ; SPy ) '|' ( SQx ; .. ; SQy )" :=
  (mk_funspec (pair (cons u%formals .. (cons v%formals nil) ..) tz) cc_default (atomic_spec_type W T)
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6, x7, x8, x9), Q, inv_names) := __a in
     PROPx (cons Px%type .. (cons Py%type nil) ..)
     (LOCALx (cons Lx%type .. (cons Ly%type nil) ..)
     (SEPx (cons (atomic_shift(inv_names := inv_names) (fun x => S2) Ei Eo (fun x r => fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) Q) (cons S1x%logic .. (cons S1y%logic nil) ..)))))
   (fun (ts: list Type) (__a : functors.MixVariantFunctor._functor (dependent_type_functor_rec ts W) mpred * (T -> mpred) * invG) => let '((x1, x2, x3, x4, x5, x6, x7, x8, x9), Q, inv_names) := __a in
    EX r : T,
     PROP () LOCAL () ((SEPx (Q r :: cons SPx .. (cons SPy nil) ..))))
   (@atomic_spec_nonexpansive_pre' _ T _ W (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in Px%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in Py%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in Lx%type) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in Ly%type) nil) ..)
      (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in S1x%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in S1y%logic) nil) ..)
      (fun ts __a x => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in S2) Ei Eo
     (fun ts __a x r => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in fold_right_sepcon (cons SQx%logic .. (cons SQy%logic nil) ..)) _ _ _ _ _)
   (atomic_spec_nonexpansive_post' W nil (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in SPx%logic) .. (cons (fun ts __a => let '(x1, x2, x3, x4, x5, x6, x7, x8, x9) := __a in SPy%logic) nil) ..) _ _)) (at level 200, x at level 0, Ei at level 0, Eo at level 0,
        x1 at level 0, x2 at level 0, x3 at level 0, x4 at level 0, x5 at level 0, x6 at level 0, x7 at level 0, x8 at level 0, x9 at level 0,
             S2 at level 0, r at level 0, T at level 0).


Global Obligation Tactic := repeat constructor || let x := fresh "x" in intros ?? x; repeat destruct x as [x ?]; simpl; auto.

Ltac start_atomic_function :=
(*  match goal with |- semax_body ?V ?G ?F ?spec =>
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
   | (fun i => _) => intros Espec DependedTypeList ((x, Q), inv_names)
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
 abbreviate_semax; simpl.*) start_function. (* legacy *)
