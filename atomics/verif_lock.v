Require Import VST.veric.rmaps.
Require Import VST.concurrency.conclib.
Require Import VST.concurrency.cancelable_invariants.
Require Import VST.floyd.library.
Require Import VST.atomics.SC_atomics_base.
Require Import VST.atomics.lock.

Section PROOFS.

#[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_lock := Tstruct _atom_int noattr.

  Definition atomic_int := Tstruct _atom_int noattr.
  Variable atomic_int_at : share -> val -> val -> mpred.
  Hypothesis atomic_int_at__ :
    forall sh v p, atomic_int_at sh v p |-- atomic_int_at sh Vundef p.
  Hypothesis atomic_int_isptr : forall sh v p, atomic_int_at sh v p |-- !! isptr p.
  Hint Resolve atomic_int_isptr : saturate_local.
  Hypothesis atomic_int_timeless : forall sh v p, fupd.timeless' (atomic_int_at sh v p).

  Definition make_atomic_spec :=
    DECLARE _make_atomic (make_atomic_spec atomic_int atomic_int_at).
  Definition free_atomic_spec :=
    DECLARE _free_atomic (free_atomic_int_spec atomic_int atomic_int_at).
  Definition atom_store_spec :=
    DECLARE _atom_store (atomic_store_spec atomic_int atomic_int_at).
  Definition atom_CAS_spec :=
    DECLARE _atom_CAS (atomic_CAS_spec atomic_int atomic_int_at).

  Definition inv_for_lock v R := EX b, atomic_int_at Ews (Val.of_bool b) v * if b then emp else R.

  (* Combine all the names for the lock into a single handle *)
  Definition lock_handle : Type := val * invariants.iname * ghosts.gname.

  Definition lock_inv sh (h : lock_handle) R := let '(v, i, g) := h in cinvariant i g (inv_for_lock v R) * cinv_own g sh.

  Lemma lock_inv_share_join : forall sh1 sh2 sh3 h R, sepalg.join sh1 sh2 sh3 ->
    lock_inv sh1 h R * lock_inv sh2 h R = lock_inv sh3 h R.
  Proof.
    intros; unfold lock_inv, cinvariant; destruct h as ((?, ?), ?).
    rewrite <- !sepcon_assoc, (sepcon_comm (_ * cinv_own _ _)), !sepcon_assoc.
    unfold cinv_own at 3 4; erewrite <- own_op by eauto.
    rewrite <- sepcon_assoc; f_equal.
    symmetry; apply invariants.invariant_dup.
  Qed.

  Lemma lock_inv_super_non_expansive : forall sh h R n,
    compcert_rmaps.RML.R.approx n (lock_inv sh h R) = compcert_rmaps.RML.R.approx n (lock_inv sh h (compcert_rmaps.RML.R.approx n R)).
  Proof.
    intros; unfold lock_inv; destruct h as ((?, ?), ?).
    rewrite !approx_sepcon; f_equal.
    rewrite cinvariant_super_non_expansive; setoid_rewrite cinvariant_super_non_expansive at 2; do 2 f_equal.
    unfold inv_for_lock.
    rewrite !approx_exp; f_equal; extensionality.
    rewrite !approx_sepcon; f_equal.
    destruct x; auto.
    rewrite approx_idem; auto.
  Qed.

  Definition ptr_of (h : lock_handle) := let '(v, i, g) := h in v.

  Program Definition makelock_spec :=
    DECLARE _makelock
    TYPE (ProdType (ConstType globals) Mpred) WITH gv: globals, R : mpred
    PRE [ ]
       PROP ()
       PARAMS () GLOBALS (gv)
       SEP (mem_mgr gv)
    POST [ tptr t_lock ] EX h,
       PROP ()
       RETURN (ptr_of h)
       SEP (mem_mgr gv; lock_inv Tsh h R).
  Next Obligation.
  Proof.
    repeat intro.
    destruct x; simpl.
    reflexivity.
  Qed.
  Next Obligation.
  Proof.
    repeat intro.
    destruct x; simpl.
    rewrite !approx_exp; f_equal; extensionality.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; do 2 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    f_equal; apply lock_inv_super_non_expansive.
  Qed.

  Program Definition freelock_spec :=
    DECLARE _freelock
    TYPE (ProdType (ConstType _) Mpred)
    WITH h : _, R : mpred
    PRE [ tptr t_lock ]
     PROP ()
     PARAMS (ptr_of h)
     SEP (weak_exclusive_mpred R && emp; lock_inv Tsh h R; R)
   POST[ tvoid ]
     PROP ()
     LOCAL ()
     SEP (R).
  Next Obligation.
  Proof.
    repeat intro.
    destruct x; simpl.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; do 3 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    f_equal.
    { apply (nonexpansive_super_non_expansive (fun R => weak_exclusive_mpred R && emp))%logic.
      apply (conj_nonexpansive (fun R => weak_exclusive_mpred R)%logic).
      - apply exclusive_mpred_nonexpansive.
      - apply const_nonexpansive. }
    f_equal. apply lock_inv_super_non_expansive.
  Qed.
  Next Obligation.
  Proof.
    repeat intro.
    destruct x; simpl.
    unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    reflexivity.
  Qed.

  Program Definition acquire_spec :=
    DECLARE _acquire
    TYPE (ProdType (ConstType _) Mpred)
    WITH sh : _, h : _, R : mpred
    PRE [ tptr t_lock ]
       PROP (readable_share sh)
       PARAMS (ptr_of h)
       SEP (lock_inv sh h R)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (lock_inv sh h R; R).
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as ((?, ?), ?); simpl.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; do 3 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    apply lock_inv_super_non_expansive.
  Qed.
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as ((?, ?), ?); simpl.
    unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    f_equal. apply lock_inv_super_non_expansive.
  Qed.

  Program Definition release_spec :=
    DECLARE _release
    TYPE (ProdType (ConstType _) Mpred)
    WITH sh : _, h : _, R : mpred
    PRE [ tptr t_lock ]
       PROP (readable_share sh)
       PARAMS (ptr_of h)
       SEP (weak_exclusive_mpred R && emp; lock_inv sh h R; R)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (lock_inv sh h R).
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as ((?, ?), ?); simpl.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; do 3 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    f_equal.
    { apply (nonexpansive_super_non_expansive (fun R => weak_exclusive_mpred R && emp))%logic.
      apply (conj_nonexpansive (fun R => weak_exclusive_mpred R)%logic).
      - apply exclusive_mpred_nonexpansive.
      - apply const_nonexpansive. }
    f_equal; apply lock_inv_super_non_expansive.
  Qed.
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as ((?, ?), ?); simpl.
    unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    apply lock_inv_super_non_expansive.
  Qed.

  Definition Gprog : funspecs :=
    ltac:(with_library prog [make_atomic_spec; atom_store_spec; atom_CAS_spec;
                             free_atomic_spec; makelock_spec; freelock_spec;
                             release_spec; acquire_spec]).

  Lemma body_makelock: semax_body Vprog Gprog f_makelock makelock_spec.
  Proof.
    start_function.
    forward_call (vint 1).
    Intros p.
    viewshift_SEP 0 (EX i g, lock_inv Tsh (p, i, g) R).
    { go_lower.
      unfold lock_inv.
      eapply derives_trans, cinv_alloc.
      unfold inv_for_lock.
      eapply derives_trans, now_later.
      Exists true; cancel. }
    simpl.
    forward.
    Exists (p, i, g); unfold lock_inv; entailer!.
  Qed.

  #[local] Hint Resolve Ensembles.Full_intro : core.

  Lemma body_freelock: semax_body Vprog Gprog f_freelock freelock_spec.
  Proof.
    start_function.
    destruct h as ((p, i), g).
    viewshift_SEP 1 (|> inv_for_lock p R).
    { go_lower.
      apply cinv_cancel; auto. }
    unfold inv_for_lock.
    rewrite (later_exp' _ true); Intros b.
    assert_PROP (is_pointer_or_null p) by entailer!.
    forward_call (p).
    - EExists; cancel.
    - destruct b; [entailer!|].
      + apply andp_left2; auto.
      + eapply derives_trans, FF_left.
        entailer!.
        apply weak_exclusive_conflict.
  Qed.

  Lemma body_release: semax_body Vprog Gprog f_release release_spec.
  Proof.
    start_function.
    forward_call (ptr_of h, vint 0, @Ensembles.Full_set invariants.iname, @Ensembles.Empty_set invariants.iname, lock_inv sh h R).
    - unfold lock_inv; destruct h as ((p, i), g).
      subst Frame; instantiate (1 := []); simpl fold_right_sepcon; cancel.
      rewrite cinvariant_dup at 1.
      sep_apply (cinv_open Ensembles.Full_set); auto.
      repeat sep_apply fupd_frame_r; apply fupd_elim.
      unfold inv_for_lock at 1.
      rewrite (later_exp' _ true); Intros b; destruct b.
      + rewrite sepcon_emp, !sepcon_assoc; sep_eapply fupd_timeless; auto; repeat sep_eapply fupd_frame_r; apply fupd_elim.
        sep_apply atomic_int_at__.
        eapply derives_trans, fupd_mask_intro_all; rewrite <- wand_sepcon_adjoint.
        Exists Ews; entailer!.
        rewrite <- wand_sepcon_adjoint.
        sep_apply fupd_frame_l; repeat sep_apply fupd_frame_r; apply fupd_elim.
        unfold ptr_of; sep_apply (modus_ponens_wand' (R * atomic_int_at Ews (vint 0) p)).
        { unfold inv_for_lock.
          eapply derives_trans, now_later.
          Exists false; cancel. }
        repeat sep_apply fupd_frame_r; apply fupd_mono; cancel.
        apply andp_left2; auto.
      + eapply derives_trans, except_0_fupd; apply orp_right1.
        rewrite !sepcon_assoc; eapply derives_trans; [apply sepcon_derives, now_later; apply derives_refl|].
        rewrite <- later_sepcon; apply later_derives.
        sep_apply weak_exclusive_conflict.
        rewrite FF_sepcon; auto.
    - hnf; inversion 1.
    - entailer!.
  Qed.

  Lemma body_acquire: semax_body Vprog Gprog f_acquire acquire_spec.
  Proof.
    start_function.
    forward.
    forward_loop (PROP ( )
                       LOCAL (temp _b (vint 0); lvar _expected tint v_expected;
                              temp _lock (ptr_of h))
                       SEP (data_at_ Tsh tint v_expected; lock_inv sh h R)).
    { entailer!. }
    forward.
    forward_call
      (ptr_of h, Tsh, v_expected, (vint 0), (vint 1), @Ensembles.Full_set invariants.iname, @Ensembles.Empty_set invariants.iname,
            fun v':val =>
              lock_inv sh h R * if (eq_dec v' (vint 0)) then |> R else emp).
    - unfold lock_inv; destruct h as ((p, i), g).
      subst Frame; instantiate (1 := []); simpl fold_right_sepcon; cancel.
      rewrite cinvariant_dup at 1.
      sep_apply (cinv_open Ensembles.Full_set); auto.
      repeat sep_apply fupd_frame_r; apply fupd_elim.
      unfold inv_for_lock at 1.
      rewrite (later_exp' _ true); Intros b.
      rewrite later_sepcon; sep_eapply fupd_timeless; auto; repeat sep_eapply fupd_frame_r; apply fupd_elim.
      eapply derives_trans, fupd_mask_intro_all; rewrite <- wand_sepcon_adjoint.
      Exists Ews (Val.of_bool b); unfold ptr_of; entailer!.
      rewrite <- wand_sepcon_adjoint.
      sep_apply fupd_frame_l; repeat sep_apply fupd_frame_r; apply fupd_elim.
      destruct b; simpl eq_dec.
      + rewrite !if_false by discriminate.
        sep_eapply fupd_timeless; [apply fupd.emp_timeless|]; repeat sep_eapply fupd_frame_r; apply fupd_elim.
        rewrite emp_sepcon.
        sep_apply (modus_ponens_wand' (atomic_int_at Ews (Val.of_bool true) p)).
        { unfold inv_for_lock.
          eapply derives_trans, now_later.
          Exists true; cancel. }
        repeat sep_apply fupd_frame_r; apply fupd_mono; cancel.
      + rewrite !if_true by auto.
        sep_apply (modus_ponens_wand' (atomic_int_at Ews (vint 1) p)).
        { unfold inv_for_lock.
          eapply derives_trans, now_later.
          Exists true; cancel. }
        repeat sep_apply fupd_frame_r; apply fupd_mono; cancel.
    - hnf; inversion 1.
    - Intros r. if_tac; forward_if; try discriminate; try contradiction.
      + forward. entailer!.
      + forward. entailer!.
  Qed.

End PROOFS.
