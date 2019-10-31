(* Specifications for locks for use with general invariants, in the style of TaDA *)
Require Import VST.veric.rmaps.
Require Import VST.veric.compcert_rmaps.
Require Import VST.progs.ghosts.
Require Import VST.progs.conclib.
Require Export VST.progs.invariants.
Require Export VST.progs.fupd.
Require Export VST.atomics.general_atomics.

Section locks.

Context {CS : compspecs}.

Parameters (locked unlocked : val -> mpred). (* instantiation depends on the lock implementation *)

Definition makelock_spec :=
  WITH p : val
  PRE [ 1%positive OF tptr tvoid ]
   PROP ()
   LOCAL (temp 1%positive p)
   SEP (data_at_ Ews tlock p)
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (locked p).

Definition freelock_spec :=
  WITH p : val
  PRE [ 1%positive OF tptr tvoid ]
   PROP ()
   LOCAL (temp 1%positive p)
   SEP (locked p)
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (data_at_ Ews tlock p).

Program Definition acquire_spec :=
  ATOMIC TYPE (ConstType _) OBJ l INVS empty top
  WITH p : val
  PRE [ 1%positive OF tptr tvoid ]
    PROP (True)
    LOCAL (temp 1%positive p)
    SEPS (seplog.emp) | ((!!(l = false) && locked p) || (!!(l = true) && unlocked p))
  POST [ tvoid ]
    PROP ()
    LOCAL ()
    SEP (!!(l = true) && locked p).

Program Definition release_spec :=
  ATOMIC TYPE (ConstType _) NO_OBJ INVS empty top
  WITH p : val
  PRE [ 1%positive OF tptr tvoid ]
    PROP (True)
    LOCAL (temp 1%positive p)
    SEPS (seplog.emp) | (locked p)
  POST [ tvoid ]
    PROP ()
    LOCAL ()
    SEP (unlocked p).


Definition lock_inv' {A : Type} lock g (a : A) R := (unlocked lock * ghost_part_ref(P := discrete_PCM A) g Tsh a a * |>R a) ||
  (locked lock * ghost_part(P := discrete_PCM A) g Tsh a).

Lemma lock_inv'_nonexpansive : forall {A} n x g x0 _f,
  approx n (lock_inv' x g x0 _f) = approx n (lock_inv' x g x0 (λ a : A, approx n (_f a))).
Proof.
  intros; unfold lock_inv'.
  rewrite !approx_orp !approx_sepcon; f_equal; f_equal.
  destruct n; [rewrite !approx_0; auto|].
  rewrite !approx_later; f_equal.
  change (approx n (approx (S n) (_f x0))) with ((approx n oo approx (S n)) (_f x0)).
  rewrite -> approx_oo_approx'; auto.
Qed.

(* can we make A a dependent type argument? *)
Program Definition acquire_spec' {A : Type} :=
  ATOMIC TYPE (ProdType (ConstType (_ * _)) (ArrowType (ConstType A) Mpred)) OBJ a INVS empty top
  WITH p : val, g : gname, R : A -> mpred
  PRE [ 1%positive OF tptr tvoid ]
    PROP (True)
    LOCAL (temp 1%positive p)
    SEPS (seplog.emp) | (lock_inv' p g a R)
  POST [ tvoid ]
    PROP ()
    LOCAL ()
    SEP (lock_inv' p g a R; ghost_reference(P := discrete_PCM A) g a; |>R a).
Next Obligation.
  let x := fresh "x" in intros ??? x; repeat destruct x as [x ?]; simpl; intros.
  apply lock_inv'_nonexpansive.
Qed.
Next Obligation.
  let x := fresh "x" in intros ??? x; repeat destruct x as [x ?]; simpl; intros.
  rewrite !approx_sepcon; f_equal.
  - apply lock_inv'_nonexpansive.
  - f_equal; f_equal.
    destruct n; [rewrite !approx_0; auto|].
    rewrite !approx_later; f_equal.
   change (approx n (approx (S n) (_f x0))) with ((approx n oo approx (S n)) (_f x0)).
    rewrite -> approx_oo_approx'; auto.
Qed.
Next Obligation.
  let x := fresh "x" in intros ??? x; repeat destruct x as [x ?]; simpl; intros; auto.
Qed.
Next Obligation.
  let x := fresh "x" in intros ??? x; repeat destruct x as [x ?]; simpl; intros; auto.
Qed.
Next Obligation.
  let x := fresh "x" in intros ??? x; repeat destruct x as [x ?]; simpl; intros; auto.
Qed.
Next Obligation.
  let x := fresh "x" in intros ??? x; repeat destruct x as [x ?]; simpl; intros; auto.
Qed.

Lemma acquire_sub : forall {A : Type}, funspec_sub acquire_spec (@acquire_spec' A).
Proof.
  intro; apply subsume_subsume.
  unfold funspec_sub', acquire_spec, acquire_spec'; intros; repeat (split; auto); intros.
  destruct x2 as ((((p, g), R), Q), inv_names).
  simpl funsig_of_funspec.
  Exists (@nil Type) (p, Q, inv_names) seplog.emp.
  simpl; intro.
  unfold liftx; simpl.
  unfold lift.
  rewrite emp_sepcon.
  apply andp_right.
  - apply andp_left2.
    unfold PROPx, LOCALx, SEPx; simpl; entailer!.
    apply andp_derives; auto.
    unfold atomic_shift.
    Intros P; Exists P; cancel.
    apply andp_derives; auto.
    apply wand_derives; auto.
    iIntros ">H !>".
    iDestruct "H" as (a) "[lock Hclose]".
    unfold lock_inv' at 1; iDestruct "lock" as "[[[u a] R] | [l a]]".
    + iExists true; iSplitL "u"; first by iRight; iFrame.
      iSplit.
      * iIntros "[[% ?] | [% ?]]"; try discriminate.
        iApply "Hclose".
        unfold lock_inv'; iLeft; iFrame.
      * iIntros (_) "[[_ l] _]".
        iDestruct "Hclose" as "[_ Hclose]"; iApply ("Hclose" $! tt).
        rewrite <- ghost_part_ref_join; iDestruct "a" as "[? ?]"; iFrame.
        unfold lock_inv'; iRight; iFrame.
    + iExists false; iSplitL "l"; first by iLeft; iFrame.
      iSplit.
      * iIntros "[[% ?] | [% ?]]"; try discriminate.
        iApply "Hclose".
        unfold lock_inv'; iRight; iFrame.
      * iIntros (_) "[[% l] _]"; discriminate.
  - apply prop_right; intros.
    apply andp_left2; rewrite emp_sepcon; auto.
Qed.

Program Definition release_spec' {A : Type} :=
  ATOMIC TYPE (ProdType (ConstType (_ * _ * _ * _)) (ArrowType (ConstType A) Mpred)) OBJ a INVS empty top
  WITH p : val, g : gname, b : A, b' : A, R : A -> mpred
  PRE [ 1%positive OF tptr tvoid ]
    PROP (True)
    LOCAL (temp 1%positive p)
    SEPS (ghost_reference(P := discrete_PCM A) g b; |>R b') | (lock_inv' p g a R)
  POST [ tvoid ]
    PROP ()
    LOCAL ()
    SEP (!!(a = b) && lock_inv' p g b' R).
Next Obligation.
  let x := fresh "x" in intros ?? x; repeat destruct x as [x ?]; simpl; intros.
  destruct n; [rewrite !approx_0; auto|].
  rewrite !approx_later; f_equal.
  change (approx n (approx (S n) (_f a))) with ((approx n oo approx (S n)) (_f a)).
  rewrite -> approx_oo_approx'; auto.
Qed.
Next Obligation.
  let x := fresh "x" in intros ??? x; repeat destruct x as [x ?]; simpl; intros.
  rewrite lock_inv'_nonexpansive; auto.
Qed.
Next Obligation.
  let x := fresh "x" in intros ??? x; repeat destruct x as [x ?]; simpl; intros; auto.
  rewrite !sepcon_emp !approx_andp lock_inv'_nonexpansive; auto.
Qed.
Next Obligation.
  let x := fresh "x" in intros ??? x; repeat destruct x as [x ?]; simpl; intros; auto.
  Qed.
Next Obligation.
  let x := fresh "x" in intros ??? x; repeat destruct x as [x ?]; simpl; intros; auto.
Qed.
Next Obligation.
  let x := fresh "x" in intros ??? x; repeat destruct x as [x ?]; simpl; intros; auto.
Qed.
Next Obligation.
  let x := fresh "x" in intros ??? x; repeat destruct x as [x ?]; simpl; intros; auto.
Qed.

Lemma release_sub : forall {A : Type}, funspec_sub release_spec (@release_spec' A).
Proof.
  intro; apply subsume_subsume.
  unfold funspec_sub', release_spec, release_spec'; intros; repeat (split; auto); intros.
  destruct x2 as ((((((p, g), b), b'), R), Q), inv_names).
  simpl funsig_of_funspec.
  Exists (@nil Type) (p, Q, inv_names) seplog.emp.
  simpl; intro.
  unfold liftx; simpl.
  unfold lift.
  rewrite emp_sepcon.
  apply andp_right.
  - apply andp_left2.
    unfold PROPx, LOCALx, SEPx; simpl; entailer!.
    apply andp_derives; auto.
    unfold atomic_shift.
    Intros P; Exists (P * ghost_reference(P := discrete_PCM A) g b * R b').
    rewrite !later_sepcon; cancel.
    apply andp_derives; auto.
    iIntros "H [[P >b] R]".
    iMod ("H" with "P") as (a) "[lock Hclose]"; subst.
    iIntros "!>"; iExists tt.
    unfold lock_inv' at 1; iDestruct "lock" as "[[[u a'] R'] | [l a]]".
    + iCombine "b a'" as "a".
      iPoseProof (own_valid_2(RA := ref_PCM (discrete_PCM A)) with "a") as "%".
      hnf in H.
      destruct H as ((?, ?) & J & _).
      inv J; simpl in *.
      inv H0.
      inv H3.
    + iFrame; iSplit.
      * iIntros "l".
        iMod ("Hclose" with "[l a]").
        { iFrame; unfold lock_inv'; iRight; iFrame. }
        iFrame; auto.
      * iIntros (_) "u".
        iCombine "a b" as "a".
        iPoseProof (ref_sub(P := discrete_PCM A) with "a") as "%".
        rewrite eq_dec_refl in H; subst.
        setoid_rewrite ghost_part_ref_join.
        iMod (ref_update(P := discrete_PCM A) with "a").
        iDestruct "Hclose" as "[_ Hclose]"; iApply ("Hclose" $! tt).
        iSplit; auto; iSplit; auto.
        unfold lock_inv'; iLeft; iFrame.
  - apply prop_right; intros.
    apply andp_left2; rewrite emp_sepcon; auto.
Qed.

End locks.
