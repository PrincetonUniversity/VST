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

Definition my_half {A} g (a : A) := ghost_part(P := discrete_PCM A) Tsh a g.
Definition public_half {A} g (a : A) := ghost_reference(P := discrete_PCM A) a g.

Lemma public_update : forall {A} g (a b a' : A),
  (my_half g a * public_half g b |-- !!(b = a) && |==> my_half g a' * public_half g a')%I.
Proof.
  intros.
  iIntros "H".
  iPoseProof (ref_sub(P := discrete_PCM A) with "H") as "%".
  rewrite eq_dec_refl in H; subst.
  iSplit; auto.
  rewrite !ghost_part_ref_join.
  iApply (ref_update(P := discrete_PCM A)); eauto.
Qed.

Definition sync_inv {A} g R := EX a : A, R a * my_half g a.
(*Definition lock_syncer {A} sh p g R := lock_inv sh p (EX a : A, R a * ghost_reference(P := discrete_PCM A) a g).

Lemma lock_syncer_nonexpansive : forall {A} n sh p g (R : A -> mpred),
  approx n (lock_syncer sh p g R) = approx n (lock_syncer sh p g (fun a => approx n (R a))).
Proof.
  intros; unfold lock_syncer.
  etransitivity; [apply nonexpansive_super_non_expansive, nonexpansive_lock_inv|].
  etransitivity; [|symmetry; apply nonexpansive_super_non_expansive, nonexpansive_lock_inv].
  f_equal; f_equal.
  rewrite !approx_exp; f_equal; extensionality.
  rewrite !approx_sepcon approx_idem; auto.
Qed.

Definition makelock_sync_type := ProdType (ProdType (ConstType (val * share)) (ArrowType (DependentType 0) Mpred)) (DependentType 0).

Program Definition makelock_sync_spec :=
  TYPE makelock_sync_type WITH p : val, sh : share, R : _ -> mpred, x : _
  PRE [ 1%positive OF tptr tvoid ]
    PROP (writable_share sh)
    LOCAL (temp 1%positive p)
    SEP (data_at_ sh tlock p)
  POST [ tvoid ]
   EX g : gname,
    PROP ()
    LOCAL ()
    SEP (lock_syncer sh p g R; ghost_part_ref(P := discrete_PCM _) Tsh x x g).
Next Obligation.
Proof.
  intros; rewrite !approx_exp; f_equal; extensionality.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp !approx_sepcon; f_equal; f_equal; f_equal.
  apply lock_syncer_nonexpansive.
Qed.

Definition acquire_sync_type := ProdType (ConstType (val * share * gname))
  (ArrowType (DependentType 0) Mpred).

(* What's the distinction between R and a (ϕ and α in mk_sync)? R is in the sync invariant, while a is in the view shift. *)
(* More importantly, a must be intuitionistic! *)

Program Definition acquire_sync_spec :=
  TYPE acquire_sync_type WITH p : val, sh : share, g : gname, R : _ -> mpred
  PRE [ 1%positive OF tptr tvoid ]
    PROP (readable_share sh)
    LOCAL (temp 1%positive p)
    SEP (lock_syncer sh p g R)
  POST [ tvoid ]
   EX x : _,
    PROP ()
    LOCAL ()
    SEP (lock_syncer sh p g R; R x; ghost_part(P := discrete_PCM _) Tsh x g).
Next Obligation.
Proof.
  intros.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp !approx_sepcon; f_equal; f_equal; f_equal.
  apply lock_syncer_nonexpansive.
Qed.
Next Obligation.
Proof.
  intros; rewrite !approx_exp; f_equal; extensionality.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp !approx_sepcon !approx_idem; f_equal; f_equal; f_equal.
  apply lock_syncer_nonexpansive.
Qed.*)

Definition release_sync_type := ProdType (ProdType (ProdType (ConstType (val * share * gname))
  (ArrowType (DependentType 0) Mpred)) (DependentType 0)) (DependentType 0).

(* Don't we still need an abort spec for release as well? We should just be able to use the normal release spec. *)
Program Definition release_sync_spec :=
  ATOMIC TYPE release_sync_type OBJ x INVS empty top
  WITH p : val, sh : share, g : gname, R : _ -> mpred, x0 : _, x' : _
  PRE [ 1%positive OF tptr tvoid ]
    PROP (readable_share sh)
    LOCAL (temp 1%positive p)
    SEPS (lock_inv sh p (sync_inv g R); R x'; my_half g x0) | (public_half g x)
  POST [ tvoid ]
    PROP ()
    LOCAL ()
    SEP (lock_inv sh p (sync_inv g R) (* private *); !!(x = x0) && public_half g x').
Next Obligation.
  - intros.
    etransitivity; [apply nonexpansive_super_non_expansive, nonexpansive_lock_inv|].
    etransitivity; [|symmetry; apply nonexpansive_super_non_expansive, nonexpansive_lock_inv].
    f_equal; f_equal.
    rewrite !approx_exp; f_equal; extensionality.
    rewrite !approx_sepcon approx_idem; auto.
  - rewrite !approx_idem; auto.
Qed.
Next Obligation.
Proof.
  intros.
  rewrite !approx_sepcon; f_equal.
  etransitivity; [apply nonexpansive_super_non_expansive, nonexpansive_lock_inv|].
  etransitivity; [|symmetry; apply nonexpansive_super_non_expansive, nonexpansive_lock_inv].
  f_equal; f_equal.
  rewrite !approx_exp; f_equal; extensionality.
  rewrite !approx_sepcon approx_idem; auto.
Qed.

(*Lemma makelock_sync : funspec_sub (makelock_spec _) makelock_sync_spec.
Proof.
  apply subsume_subsume.
  unfold funspec_sub', makelock_spec, makelock_sync_spec; intros; repeat (split; auto); intros.
  destruct x2 as (((p, sh), R), x).
  simpl; intro.
  iIntros "H".
  iMod (own_alloc(RA := ref_PCM (discrete_PCM _)) (Some (Tsh, x), Some x) NoneP with "[]") as (g) "g"; auto.
  { simpl; split; auto with share; apply @self_completable. }
  iExists (@nil Type), (p, sh, EX a, R a * ghost_reference(P := discrete_PCM _) a g), (ghost_part_ref(P := discrete_PCM _) Tsh x x g).
  iIntros "!>"; iSplit.
  - iSplitL "g"; [auto|].
    iDestruct "H" as "(_ & H)".
    unfold PROPx, LOCALx, SEPx; simpl.
    iDestruct "H" as "(? & ? & H)".
    iSplit; auto; iSplit; auto.
  - iPureIntro.
    iIntros (?) "[_ [g H]]".
    match goal with |-context[(|==> ?P)%logic] => change (|==>P)%logic with (|==>P)%I end.
    iIntros "!>"; iExists g.
    unfold PROPx, LOCALx, SEPx; simpl.
    iDestruct "H" as "(? & ? & H & _)".
    iSplit; auto; iSplit; auto.
    iFrame.
Qed.

Lemma acquire_sync : funspec_sub acquire_spec acquire_sync_spec.
Proof.
  apply subsume_subsume.
  unfold funspec_sub', acquire_spec, acquire_sync_spec; intros; repeat (split; auto); intros.
  destruct x2 as (((((((p, sh), g), R), a), b), Q), inv_names).
  simpl; intro.
  eapply derives_trans, ghost_seplog.bupd_intro.
  Exists (@nil Type) (p, sh, EX a, R a * ghost_reference(P := discrete_PCM _) a g)
    (atomic_shift(inv_names := inv_names) (fun x => a x * ghost_part(P := discrete_PCM _) Tsh x g || ghost_reference(P := discrete_PCM _) x g) ∅ ⊤ b (fun _ => Q)).
  apply andp_right.
  - apply andp_left2; unfold acquire_pre, PROPx, LOCALx, SEPx; simpl; entailer!.
    unfold local, lift1; simpl.
    rewrite -sepcon_andp_prop' sepcon_comm; apply derives_refl.
  - apply prop_right; intros.
    match goal with |- _ |-- (|==> ?Q)%logic => apply derives_trans with (@bi_fupd_fupd _ (@mpred_bi_fupd inv_names) top top Q) end.
    unfold PROPx, LOCALx, SEPx; simpl; iIntros "(_ & AS & ? & ? & ? & R & _)".
    iDestruct "R" as (x') "[? g]".
    iDestruct "AS" as (P) "[P AS]".
    iDestruct (cored_dup with "AS") as "[AS ?]".
    iMod ("AS" with "P") as (x1) "[a H]".
    iDestruct "a" as "[[? g'] | g']".
    iCombine "g' g" as "g".
    iPoseProof (ref_sub(P := discrete_PCM _) with "g") as "%".
    rewrite eq_dec_refl in H; subst.
    iDestruct "g" as "[? g]".
    iDestruct "H" as "[H _]"; iMod ("H" with "[g]") as "H"; first by iRight.
    iIntros "!>"; iExists x'.
    iSplit; auto; iSplit; auto; iFrame.
    rewrite sepcon_emp; iExists P; iFrame.
    { iCombine "g g'" as "g".
      iPoseProof (own_valid_2(RA := ref_PCM (discrete_PCM _)) with "g") as "%".
      hnf in H.
      destruct H as ((?, ?) & J & _).
      inv J; simpl in *.
      inv H0.
      inv H3. }
    admit.
Admitted.*)

Lemma release_sync : funspec_sub release_spec release_sync_spec.
Proof.
  apply subsume_subsume.
  unfold funspec_sub', release_spec, release_sync_spec; intros; repeat (split; auto); intros.
  destruct x2 as (((((((p, sh), g), R), x0), x'), Q), inv_names).
  simpl; intro.
  match goal with |- _ |-- (|==> ?Q)%logic => apply derives_trans with (@bi_fupd_fupd _ (@mpred_bi_fupd inv_names) top top Q) end.
  iIntros "[_ H]".
  unfold release_pre, PROPx, LOCALx, SEPx; simpl.
  iDestruct "H" as "(? & ? & AS & ? & R & g & _)".
  iDestruct "AS" as (P) "[P AS]"; iMod ("AS" with "P") as (x1) "[a H]".
  iPoseProof (public_update(A := nth 0 ts2 unit) with "[$g $a]") as "[% >[? g]]".
  iDestruct "H" as "[_ H]".
  iMod ("H" $! tt with "[$g]").
  { admit. }
  iIntros "!>".
  iExists (@nil Type), (p, sh, sync_inv(A := nth 0 ts2 unit) g R), Q.
  iFrame.
  iSplit.
  - iSplitL "".
    { iSplit; auto; iApply exclusive_weak_exclusive; auto.
      iIntros "[P1 P2]"; iDestruct "P1" as (a1) "[? g1]"; iDestruct "P2" as (a2) "[? g2]".
      iCombine "g1 g2" as "g".
      iPoseProof (own_valid_2(RA := ref_PCM (discrete_PCM _)) with "g") as "%".
      hnf in H0.
      destruct H0 as ((?, ?) & J & _).
      inv J; simpl in *.
      destruct g0 as [(?, ?)|]; auto.
      destruct H0 as (? & ? & J & ?).
      apply join_Tsh in J as []; contradiction. }
    rewrite sepcon_emp.
    iExists x'; iFrame.
  - iPureIntro; iIntros (?) "(_ & Q & H)".
    match goal with |-context[(|==>?Q)%logic] => change (|==>Q)%logic with (|==>Q)%I end.
    iIntros "!>".
    iFrame.
    admit.
Admitted.

(*Parameters (locked unlocked : val -> mpred). (* instantiation depends on the lock implementation *)
Axioms (locked_timeless : forall p, Timeless (locked p)) (unlocked_timeless : forall p, Timeless (unlocked p)).
Axioms (locked_isptr : forall p, locked p |-- !!isptr p) (unlocked_isptr : forall p, unlocked p |-- !!isptr p).

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
    SEPS (emp) | ((!!(l = false) && locked p) || (!!(l = true) && unlocked p))
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
    SEPS (emp) | (locked p)
  POST [ tvoid ]
    PROP ()
    LOCAL ()
    SEP (unlocked p).


Definition lock_inv' {A : Type} lock g (a : A) R := (unlocked lock * ghost_part_ref(P := discrete_PCM A) Tsh a a g * R a) ||
  (locked lock * ghost_part(P := discrete_PCM A) Tsh a g).

Global Instance lock_inv'_timeless {A} lock g (a : A) R (HR : forall a, Timeless (R a)): Timeless (lock_inv' lock g a R).
Proof.
  unfold lock_inv'.
  apply (@bi.or_timeless mpredSI).
  - apply (@bi.sep_timeless mpredSI); auto.
    apply (@bi.sep_timeless mpredSI); [apply unlocked_timeless | apply _].
  - apply (@bi.sep_timeless mpredSI); [apply locked_timeless | apply _].
Qed.

Lemma lock_inv'_nonexpansive : forall {A} n x g x0 _f,
  approx n (lock_inv' x g x0 _f) = approx n (lock_inv' x g x0 (λ a : A, approx n (_f a))).
Proof.
  intros; unfold lock_inv'.
  rewrite !approx_orp !approx_sepcon approx_idem; auto.
Qed.

Definition timeless_inv {A} R : mpred := ALL a : A, |> R a -* sbi_except_0 (R a).

Lemma timeless_inv_nonexpansive: forall {A} n (R : A -> mpred),
  approx n (timeless_inv R) = approx n (timeless_inv (fun a => approx n (R a))).
Proof.
  intros; unfold timeless_inv.
  rewrite allp_nonexpansive; setoid_rewrite allp_nonexpansive at 2; f_equal; f_equal; extensionality.
  rewrite wand_nonexpansive; setoid_rewrite wand_nonexpansive at 2; f_equal; f_equal.
  - apply later_nonexpansive.
  - unfold sbi_except_0.
    rewrite !approx_orp approx_idem; auto.
Qed.

Lemma timeless_inv_timeless : forall {A} (R : A -> mpred) {H : forall a, Timeless (R a)},
  emp |-- timeless_inv R && emp.
Proof.
  intros; apply andp_right; auto.
  intros; unfold timeless_inv.
  iIntros "_" (a) "R".
  iApply (timeless with "R").
Qed.

Program Definition acquire_spec' :=
  ATOMIC TYPE (ProdType (ConstType (_ * _)) (ArrowType (DependentType 0) Mpred)) OBJ a INVS empty top
  WITH p : val, g : gname, R : _
  PRE [ 1%positive OF tptr tvoid ]
    PROP (True)
    LOCAL (temp 1%positive p)
    SEPS (emp) | (lock_inv' p g a R)
  POST [ tvoid ]
    PROP ()
    LOCAL ()
    SEP (lock_inv' p g a R; ghost_reference(P := discrete_PCM _) a g; R a).
Next Obligation.
  intros; apply lock_inv'_nonexpansive.
Qed.
Next Obligation.
  intros; rewrite !approx_sepcon approx_idem; f_equal.
  apply lock_inv'_nonexpansive.
Qed.

Lemma acquire_sub : funspec_sub acquire_spec acquire_spec'.
Proof.
  apply subsume_subsume.
  unfold funspec_sub', acquire_spec, acquire_spec'; intros; repeat (split; auto); intros.
  destruct x2 as ((((p, g), R), Q), inv_names).
  simpl funsig_of_funspec.
  eapply derives_trans, ghost_seplog.bupd_intro.
  Exists (@nil Type) (p, Q, inv_names) emp.
  simpl; intro.
  unfold liftx; simpl.
  unfold lift.
  rewrite emp_sepcon.
  apply andp_right.
  - apply andp_left2.
    unfold PROPx, LOCALx, SEPx; simpl; entailer!.
    apply andp_derives; auto.
    apply atomic_shift_derives'; intros.
    iIntros "lock !>".
    unfold lock_inv' at 1. iDestruct "lock" as "[[[u a] R] | [l a]]".
    + iExists true; iSplitL "u"; first by iRight; iFrame.
      iSplit.
      * iIntros "[[% ?] | [% ?]] !>"; try discriminate.
        unfold lock_inv'; iLeft; iFrame.
      * iIntros (_) "[[_ l] _] !>".
        rewrite <- ghost_part_ref_join; iDestruct "a" as "[? ?]"; iFrame.
        unfold lock_inv'; iRight; iFrame.
    + iExists false; iSplitL "l"; first by iLeft; iFrame.
      iSplit.
      * iIntros "[[% ?] | [% ?]] !>"; try discriminate.
        unfold lock_inv'; iRight; iFrame.
      * iIntros (_) "[[% l] _]"; discriminate.
  - apply prop_right; intros.
    apply andp_left2; rewrite emp_sepcon; apply ghost_seplog.bupd_intro.
Qed.

Definition release_type' := (ProdType (ProdType (ProdType (ConstType (val * gname))
  (DependentType 0)) (DependentType 0)) (ArrowType (DependentType 0) Mpred)).

Program Definition release_spec' :=
  ATOMIC TYPE release_type' OBJ a INVS empty top
  WITH p : val, g : gname, b : _, b' : _, R : _ -> mpred
  PRE [ 1%positive OF tptr tvoid ]
    PROP (True)
    LOCAL (temp 1%positive p)
    SEPS (timeless_inv R && emp; ghost_reference(P := discrete_PCM _) b g; |>R b') | (lock_inv' p g a R)
  POST [ tvoid ]
    PROP ()
    LOCAL ()
    SEP (!!(a = b) && lock_inv' p g b' R).
Next Obligation.
  intros; rewrite !approx_andp timeless_inv_nonexpansive; auto.
  intros; rewrite later_nonexpansive; auto.
Qed.
Next Obligation.
  intros; rewrite lock_inv'_nonexpansive; auto.
Qed.
Next Obligation.
  intros; rewrite !sepcon_emp !approx_andp lock_inv'_nonexpansive; auto.
Qed.

Lemma release_sub : funspec_sub release_spec release_spec'.
Proof.
  apply subsume_subsume.
  unfold funspec_sub', release_spec, release_spec'; intros; repeat (split; auto); intros.
  destruct x2 as ((((((p, g), b), b'), R), Q), inv_names).
  simpl funsig_of_funspec.
  eapply derives_trans, ghost_seplog.bupd_intro.
  Exists (@nil Type) (p, Q, inv_names) emp.
  simpl; intro.
  unfold liftx; simpl.
  unfold lift.
  rewrite emp_sepcon.
  apply andp_right.
  - apply andp_left2.
    unfold PROPx, LOCALx, SEPx; simpl; entailer!.
    apply andp_derives; auto.
    rewrite sepcon_assoc; eapply derives_trans, atomic_shift_derives_frame_cored.
    { apply sepcon_derives; [apply derives_refl|].
      setoid_rewrite later_sepcon; apply sepcon_derives; [apply now_later | apply derives_refl]. }
    { apply andp_left2, emp_cored. }
    iIntros (a) "[[lock timeless] [>b R]] !>"; iExists tt.
    unfold lock_inv' at 1; iDestruct "lock" as "[[[u a'] R'] | [l a]]".
    + iCombine "b a'" as "a".
      iPoseProof (own_valid_2(RA := ref_PCM (discrete_PCM _)) with "a") as "%".
      hnf in H.
      destruct H as ((?, ?) & J & _).
      inv J; simpl in *.
      inv H0.
      inv H3.
    + iFrame; iSplit.
      * iIntros "l".
        iFrame; iSplitR "timeless"; auto.
        unfold lock_inv'; iRight; iFrame; auto.
      * iIntros (_) "u".
        iCombine "a b" as "a".
        iPoseProof (ref_sub(P := discrete_PCM _) with "a") as "%".
        rewrite eq_dec_refl in H; subst.
        setoid_rewrite ghost_part_ref_join.
        iMod (ref_update(P := discrete_PCM _) with "a").
        unfold timeless_inv.
        iMod ("timeless" with "R").
        iIntros "!>"; iExists tt; iFrame.
        iSplitR ""; [|by iIntros "?"].
        iSplit; auto; iSplit; auto.
        unfold lock_inv'; iLeft; iFrame.
  - apply prop_right; intros.
    apply andp_left2; rewrite emp_sepcon; apply ghost_seplog.bupd_intro.
Qed.

Definition acq_type := ProdType (ProdType (ProdType (ProdType (ConstType (val * gname))
  (ArrowType (DependentType 0) Mpred)) (ArrowType (DependentType 0) (ArrowType (DependentType 1) Mpred)))
  (ArrowType (DependentType 1) Mpred)) (ConstType invG).

Program Definition acquire_inv_spec :=
  TYPE acq_type WITH p : val, g : gname, R : _ -> mpred, b : _, Q : _, inv_names : invG
  PRE [ 1%positive OF tptr tvoid ]
    PROP (True)
    LOCAL (temp 1%positive p)
    SEP (atomic_shift (fun a => lock_inv' p g a R) empty top b Q) (* would it be simpler if this was inv? Inv isn't freeable, but atomic_shift isn't duplicable. *)
  POST [ tvoid ]
   EX a : _,
    PROP ()
    LOCAL ()
    SEP (atomic_shift (fun a => lock_inv' p g a R) empty top b Q;
            ghost_reference(P := discrete_PCM _) a g; R a).
Next Obligation.
Proof.
  intros; unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal;
    f_equal; rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  rewrite atomic_shift_nonexpansive; setoid_rewrite atomic_shift_nonexpansive at 2.
  f_equal; f_equal; repeat extensionality; rewrite ?approx_idem; auto.
  apply lock_inv'_nonexpansive.
Qed.
Next Obligation.
Proof.
  intros; rewrite !approx_exp; apply f_equal; extensionality.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
  f_equal.
  rewrite atomic_shift_nonexpansive; setoid_rewrite atomic_shift_nonexpansive at 2.
  f_equal; f_equal; repeat extensionality; rewrite ?approx_idem; auto.
  apply lock_inv'_nonexpansive.
Qed.

Lemma acquire_inv : funspec_sub acquire_spec acquire_inv_spec.
Proof.
  eapply funspec_sub_trans; [apply acquire_sub|].
  eapply stabilize0; intros ? ((?, ?), ?); intros; simpl.
  - apply f_equal2.
    { instantiate (1 := fun _ _ => _); auto. }
    apply f_equal2.
    { instantiate (1 := [fun _ '(p, _, _) => temp _ p]); auto. }
    unfold SEPx; simpl; extensionality; apply f_equal2.
    { instantiate (1 := fun ts '(p, g, R) a _ => _).
      instantiate (4 := fun ts '(p, g, R) a => _); auto. }
    { instantiate (1 := fun _ _ => emp); auto. }
  - instantiate (1 := nil); auto.
  - f_equal; f_equal.
    unfold SEPx; simpl.
    rewrite !sepcon_emp; auto.
  - extensionality; simpl.
    apply f_equal; extensionality.
    unfold PROPx, LOCALx, SEPx; simpl.
    apply f_equal2; [auto|].
    apply f_equal2; [auto|].
    rewrite !sepcon_emp.
    instantiate (1 := fun _ '(p, g, R) a => _); auto.
  - simpl.
    rewrite sepcon_emp; apply derives_refl.
Qed.

Definition rel_type := ProdType (ProdType (ProdType (ProdType (ProdType (ConstType (val * gname))
   (DependentType 0)) (ArrowType (DependentType 0) Mpred)) (ArrowType (DependentType 0) (ArrowType (DependentType 1) Mpred)))
  (ArrowType (DependentType 1) Mpred)) (ConstType invG).

(* This version of release only works if the invariant has been re-established; otherwise,
  you need to use release_spec' and show that you've reached your linearization point. *)
Program Definition release_inv_spec :=
  TYPE rel_type WITH p : val, g : gname, a : _, R : _ -> mpred, b : _ -> _ -> mpred, Q : _ -> mpred, inv_names : invG
  PRE [ 1%positive OF tptr tvoid ]
    PROP (True)
    LOCAL (temp 1%positive p)
    SEP (timeless_inv R && emp; atomic_shift (fun a => lock_inv' p g a R) empty top b Q;
            ghost_reference(P := discrete_PCM _) a g; |>R a)
  POST [ tvoid ]
    PROP ()
    LOCAL ()
    SEP (atomic_shift (fun a => lock_inv' p g a R) empty top b Q).
Next Obligation.
Proof.
  intros; unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal;
    f_equal; rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  f_equal.
  { rewrite !approx_andp timeless_inv_nonexpansive; auto. }
  f_equal.
  rewrite atomic_shift_nonexpansive; setoid_rewrite atomic_shift_nonexpansive at 2.
  f_equal; f_equal; repeat extensionality; rewrite ?approx_idem; auto.
  - apply lock_inv'_nonexpansive.
  - rewrite later_nonexpansive; auto.
Qed.
Next Obligation.
Proof.
  intros.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
  rewrite atomic_shift_nonexpansive; setoid_rewrite atomic_shift_nonexpansive at 2.
  f_equal; f_equal; repeat extensionality; rewrite ?approx_idem; auto.
  apply lock_inv'_nonexpansive.
Qed.

(* Because of this distinction, it's a bit awkward to phrase this as a stabilization. *)
Lemma release_inv : funspec_sub release_spec release_inv_spec.
Proof.
  eapply funspec_sub_trans; [apply release_sub|].
  apply subsume_subsume; unfold funspec_sub', release_spec', release_inv_spec.
  repeat split; auto; intros.
  destruct x2 as ((((((p, g), a), R), b), Q), inv_names).
  simpl funsig_of_funspec.
  set (AS := atomic_shift _ _ _ _ _).
  unfold AS, atomic_shift; Intros P.
  eapply derives_trans, ghost_seplog.bupd_intro.
  Exists ts2 (p, g, a, a, R, AS, inv_names) emp.
  simpl; intro.
  unfold liftx; simpl.
  unfold lift.
  rewrite emp_sepcon.
  apply andp_right.
  - apply andp_left2.
    unfold PROPx, LOCALx, SEPx; simpl; entailer!.
    Exists P.
    apply andp_derives; auto.
    cancel.
    sep_apply cored_dup_cored.
    apply andp_derives; auto.
    unfold ashift at 1 3.
    iIntros "[H AS] P"; iMod ("H" with "P") as (a') "[lock H]".
    iExists a'; iFrame.
    iIntros "!>"; iSplit.
    + iDestruct "AS" as "[_ e]"; iMod (cored_emp with "e") as "_".
      by iApply bi.and_elim_l.
    + iIntros (_) "[[% lock] _]"; subst.
      iMod ("H" with "lock").
      unfold AS, atomic_shift; iExists P; iFrame; auto.
  - apply prop_right; intros.
    apply andp_left2; rewrite emp_sepcon; apply ghost_seplog.bupd_intro.
Qed.

Definition makelock_type := ProdType (ProdType (ConstType val) (DependentType 0))
  (ArrowType (DependentType 0) Mpred).

Program Definition makelock_inv_spec :=
  TYPE makelock_type WITH p : val, a : _, R : _ -> mpred
  PRE [ 1%positive OF tptr tvoid ]
    PROP ()
    LOCAL (temp 1%positive p)
    SEP (data_at_ Ews tlock p)
  POST [ tvoid ]
    PROP ()
    LOCAL ()
    SEP (EX g : gname, lock_inv' p g a R * ghost_reference(P := discrete_PCM _) a g).
Next Obligation.
  intros.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
  rewrite !approx_exp; f_equal; f_equal; extensionality.
  rewrite !approx_sepcon lock_inv'_nonexpansive; auto.
Qed.

Lemma makelock_inv : funspec_sub makelock_spec makelock_inv_spec.
Proof.
  apply subsume_subsume; unfold funspec_sub', makelock_spec, makelock_inv_spec.
  repeat split; auto; intros.
  destruct x2 as ((p, a), R).
  simpl funsig_of_funspec.
  eapply derives_trans, ghost_seplog.bupd_intro.
  Exists (@nil Type) p emp.
  rewrite !emp_sepcon; apply andp_right; entailer!.
  apply andp_left2; simpl; intro.
  iIntros "[lock e]".
  rewrite sepcon_emp.
  iMod (own_alloc(RA := ref_PCM (discrete_PCM _)) (Some (Tsh, a), Some a) NoneP with "e") as (g) "g"; auto.
  { simpl; split; auto with share; apply @self_completable. }
  iExists g; unfold lock_inv'.
  setoid_rewrite <- ghost_part_ref_join.
  iDestruct "g" as "[g $]".
  iIntros "!>"; iRight; iFrame.
Qed.

Definition freelock_type := ProdType (ProdType (ProdType (ConstType (val * gname))
   (DependentType 0)) (ArrowType (DependentType 0) Mpred)) (ConstType invG).

Program Definition freelock_inv_spec :=
  TYPE freelock_type WITH p : val, g : gname, a : _, R : _ -> mpred, inv_names : invG
  PRE [ 1%positive OF tptr tvoid ]
   PROP ()
   LOCAL (temp 1%positive p)
   SEP (atomic_shift(B := unit) (fun a => lock_inv' p g a R) empty top (fun _ _ => emp) (fun _ => emp);
           ghost_reference(P := discrete_PCM _) a g)
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (data_at_ Ews tlock p)%I.
Next Obligation.
Proof.
  intros; unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal;
    f_equal; rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  f_equal.
  rewrite atomic_shift_nonexpansive; setoid_rewrite atomic_shift_nonexpansive at 2.
  f_equal; f_equal; repeat extensionality; rewrite ?approx_idem; auto.
  apply lock_inv'_nonexpansive.
Qed.

Lemma freelock_inv : funspec_sub freelock_spec freelock_inv_spec.
Proof.
  (* need to be able to do fupd in precondition of funspec_sub *)
  apply subsume_subsume; unfold funspec_sub', freelock_spec, freelock_inv_spec.
  repeat split; auto; intros.
  destruct x2 as ((((p, g), a), R), inv_names).
  simpl funsig_of_funspec.
  eapply derives_trans, ghost_seplog.bupd_intro.
  Exists ts2 p emp.
  simpl; intro.
  unfold liftx; simpl.
  unfold lift.
  rewrite emp_sepcon.
  apply andp_right.
  - apply andp_left2.
    unfold PROPx, LOCALx, SEPx; simpl; apply andp_derives; auto; apply andp_derives; auto.
    unfold atomic_shift; Intros P.
    eapply derives_trans with (|={top}=>locked p)%I; [|admit].
    iIntros "[[P H] [g _]]".
    iMod ("H" with "P") as (?) "[lock H]".
    unfold lock_inv' at 1.
    iDestruct "lock" as "[[[? g'] ?] | [$ g']]".
    + iCombine "g g'" as "g".
      iPoseProof (own_valid_2(RA := ref_PCM (discrete_PCM _)) with "g") as "%".
      hnf in H0.
      destruct H0 as ((?, ?) & J & _).
      inv J; simpl in *.
      inv H1.
      inv H4.
    + iMod (own_dealloc(RA := ref_PCM (discrete_PCM _)) with "g").
      iMod (own_dealloc(RA := ref_PCM (discrete_PCM _)) with "g'").
      iDestruct "H" as "[_ H]"; iApply ("H" $! tt); auto.
  - apply prop_right; intros.
    apply andp_left2; rewrite emp_sepcon; apply ghost_seplog.bupd_intro.
Admitted.*)

End locks.

(*Hint Resolve locked_isptr unlocked_isptr : saturate_local.*)
