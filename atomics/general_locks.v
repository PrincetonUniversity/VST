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
Axioms (locked_timeless : forall p, Timeless (locked p)) (unlocked_timeless : forall p, Timeless (unlocked p)).

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
    unfold lock_inv' at 1; iDestruct "lock" as "[[[u a] R] | [l a]]".
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
    apply andp_left2; rewrite emp_sepcon; auto.
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
    apply andp_left2; rewrite emp_sepcon; auto.
Qed.

Definition acq_type := ProdType (ProdType (ProdType (ProdType (ConstType (val * gname))
  (ArrowType (DependentType 0) Mpred)) (ArrowType (DependentType 0) (ArrowType (DependentType 1) Mpred)))
  (ArrowType (DependentType 1) Mpred)) (ConstType invG).

Program Definition acquire_inv_spec :=
  TYPE acq_type WITH p : val, g : gname, R : _ -> mpred, b : _, Q : _, inv_names : invG
  PRE [ 1%positive OF tptr tvoid ]
    PROP (True)
    LOCAL (temp 1%positive p)
    SEP (atomic_shift (fun a => lock_inv' p g a R) empty top b Q)
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
            ghost_reference(P := discrete_PCM _) a g; R a)
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
  apply lock_inv'_nonexpansive.
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
    apply andp_left2; rewrite emp_sepcon.
    apply derives_refl.
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
   EX g : gname,
    PROP ()
    LOCAL ()
    SEP (|==>lock_inv' p g a R * ghost_reference(P := discrete_PCM _) a g).
Next Obligation.
  intros.
  rewrite !approx_exp; f_equal; extensionality.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
  rewrite !approx_bupd !approx_sepcon lock_inv'_nonexpansive; auto.
Qed.

Lemma makelock_inv : funspec_sub makelock_spec makelock_inv_spec.
Proof.
  apply subsume_subsume; unfold funspec_sub', makelock_spec, makelock_inv_spec.
  repeat split; auto; intros.
  destruct x2 as ((p, a), R).
  simpl funsig_of_funspec.
  Exists (@nil Type) p emp.
  rewrite !emp_sepcon; apply andp_right; entailer!.
  rewrite <- !exp_andp2, TT_andp.
  apply andp_derives.
  { simpl; intros; entailer!. }
  simpl; intro.
  iIntros "[lock _]".
  rewrite <- exp_sepcon1, sepcon_emp.
  iMod (own_alloc(RA := ref_PCM (discrete_PCM _)) (Some (Tsh, a), Some a) NoneP with "[]") as "g"; auto.
  { simpl; split; auto with share; apply @self_completable. }
  setoid_rewrite sepcon_emp.
  SearchAbout bupd bi_sep.
  iMod "g" as (g) "g".
  iIntros "H".
  SearchAbout bupd bi_exist.
    
    hnf.
  viewshift_SEP 0 (EX g : _, ghost_part(P := discrete_PCM _) Tsh a g).
  ghost_alloc (ghost_part(P := discrete_PCM _) Tsh a).
  iIntros "H".
  setoid_rewrite TT_andp.
  SearchAbout TT andp.
  iIntros 
  - rewrite sepcon_
apply andp_left2; unfold liftx; simpl; intros.
    unfold lift; simpl.
    unfold PROPx, LOCALx, SEPx; entailer!.
    unfold local; simpl.
    unfold lift1; simpl.
    rewrite sepcon_andp_prop; apply andp_derives; auto; cancel.
  - intros; apply andp_left2.
    unfold liftx; simpl.
    unfold lift; simpl.
    ghost_alloc (ghost_part Tsh a).

    
  
    SearchAbout local andp.
  set (AS := atomic_shift _ _ _ _ _).
  unfold AS, atomic_shift; Intros P.
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
    apply andp_left2; rewrite emp_sepcon.
    apply derives_refl.
Qed.
End locks.
