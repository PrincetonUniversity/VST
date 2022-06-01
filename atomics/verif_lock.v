Require Import VST.veric.rmaps.
Require Import VST.concurrency.conclib.
Require Import VST.concurrency.ghosts.
Require Import VST.concurrency.cancelable_invariants.
Require Import VST.floyd.library.
Require Import VST.atomics.SC_atomics_base.
Require Import VST.concurrency.lock_specs.
Require Import VST.concurrency.threads.

#[export] Program Instance atom_impl : atomic_int_impl := { atomic_int := Tstruct _atom_int noattr }.
Next Obligation. Admitted.
Next Obligation. Admitted.
Axiom atomic_int_isptr : forall sh v p, atomic_int_at sh v p |-- !! isptr p.
#[export] Hint Resolve atomic_int_isptr : saturate_local.
Axiom atomic_int_timeless : forall sh v p, fupd.timeless' (atomic_int_at sh v p).
#[export] Hint Resolve atomic_int_timeless : core.

#[global] Opaque atomic_int_at.

Section PROOFS.

  #[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
  Definition Vprog : varspecs. mk_varspecs prog. Defined.

  Definition make_atomic_spec := DECLARE _make_atomic make_atomic_spec.
  Definition free_atomic_spec := DECLARE _free_atomic free_atomic_int_spec.
  Definition atom_store_spec := DECLARE _atom_store atomic_store_spec.
  Definition atom_CAS_spec := DECLARE _atom_CAS atomic_CAS_spec.

  Definition inv_for_lock v R := EX b, atomic_int_at Ews (Val.of_bool b) v * if b then emp else R.

  Definition atomic_lock_inv sh h R := let '(v, i, g) := h in !!(sh <> Share.bot /\ isptr v) && cinvariant i g (inv_for_lock v R) * cinv_own g sh.

  #[export] Program Instance atomic_impl : lock_impl := { t_lock := Tstruct _atom_int noattr; lock_handle := val * invariants.iname * ghosts.gname;
    ptr_of h := let '(v, i, g) := h in v; lock_inv := atomic_lock_inv }.
  Next Obligation.
  Proof.
    unfold atomic_lock_inv.
    apply sepcon_nonexpansive, const_nonexpansive.
    apply @conj_nonexpansive; [apply const_nonexpansive|].
    apply cinvariant_nonexpansive2.
    unfold inv_for_lock.
    apply @exists_nonexpansive; intros.
    apply sepcon_nonexpansive; [apply const_nonexpansive|].
    destruct x; [apply const_nonexpansive | apply identity_nonexpansive].
  Qed.
  Next Obligation.
  Proof.
    unfold atomic_lock_inv.
    destruct (isptr_dec v).
    rewrite !prop_true_andp; auto.
    rewrite <- !sepcon_assoc, (sepcon_comm (_ * cinv_own _ _)), !sepcon_assoc.
    unfold cinv_own at 1 2; erewrite <- own_op by eauto.
    rewrite <- sepcon_assoc; f_equal.
    symmetry; apply cinvariant_dup.
    { split; auto; intros ?; subst. apply join_Bot in H1 as []; contradiction. }
    { rewrite prop_false_andp, !FF_sepcon, prop_false_andp, FF_sepcon; auto; intros []; contradiction. }
  Qed.
  Next Obligation.
  Proof.
    unfold exclusive_mpred, atomic_lock_inv; Intros.
    unfold cinv_own; sep_apply own_op'.
    Intros ?; Intros.
    apply sepalg.join_self, identity_share_bot in H0; contradiction.
  Qed.
  Next Obligation.
  Proof.
    unfold atomic_lock_inv; entailer!.
  Qed.

  (* We can use self_part sh h * R instead of selflock sh h R. *)
  Definition self_part sh (h : lock_handle) := let '(v, i, g) := h in cinv_own g sh.

  Lemma self_part_exclusive : forall sh h, sh <> Share.bot -> exclusive_mpred (self_part sh h).
  Proof.
    intros; unfold exclusive_mpred, self_part; destruct h as ((?, ?), ?).
    unfold cinv_own; rewrite own_op'; Intros ?.
    apply sepalg.join_self, identity_share_bot in H0; contradiction.
  Qed.

  Lemma self_part_eq : forall sh1 sh2 h R, sh2 <> Share.bot -> lock_inv sh1 h (self_part sh2 h * R) * self_part sh2 h * R =
    lock_inv sh1 h (self_part sh2 h * R) * lock_inv sh2 h (self_part sh2 h * R) * R.
  Proof.
    intros.
    simpl; unfold atomic_lock_inv; destruct h as ((?, ?), ?).
    destruct (eq_dec sh1 Share.bot).
    { rewrite prop_false_andp, !FF_sepcon; auto; intros []; contradiction. }
    destruct (isptr_dec v).
    rewrite !prop_true_andp by auto.
    unfold self_part at 2; rewrite cinvariant_dup at 1.
    rewrite <- !sepcon_assoc; do 2 f_equal.
    rewrite (sepcon_comm (_ * _) (cinvariant _ _ _)), <- sepcon_assoc; reflexivity.
    { rewrite prop_false_andp, !FF_sepcon; auto; intros []; contradiction. }
  Qed.

  Definition makelock_spec := DECLARE _makelock makelock_spec.
  Definition freelock_spec := DECLARE _freelock freelock_spec.
  Definition acquire_spec := DECLARE _acquire acquire_spec.
  Definition release_spec := DECLARE _release release_spec.

  Definition Gprog : funspecs :=
    ltac:(with_library prog [make_atomic_spec; atom_store_spec; atom_CAS_spec;
                             free_atomic_spec; makelock_spec; freelock_spec;
                             release_spec; acquire_spec]).

  Lemma body_makelock: semax_body Vprog Gprog f_makelock makelock_spec.
  Proof.
    start_function.
    forward_call (vint 1).
    Intros p.
    viewshift_SEP 0 (EX i g, lock_inv Tsh (p, i, g) (R (p, i, g))).
    { go_lower; simpl.
      entailer!.
      eapply derives_trans, fupd_mono; [|apply exp_derives; intros; apply exp_derives; intros; apply sepcon_derives, derives_refl; apply andp_right, derives_refl; entailer!].
      eapply derives_trans, cinv_alloc_dep.
      unfold inv_for_lock.
      do 2 (apply allp_right; intros).
      eapply derives_trans, now_later.
      Exists true; simpl; cancel. apply derives_refl. }
    simpl.
    forward.
    simpl; Exists (p, i, g); unfold atomic_lock_inv; entailer!.
  Qed.

  #[local] Hint Resolve Ensembles.Full_intro : core.

  Lemma body_freelock: semax_body Vprog Gprog f_freelock freelock_spec.
  Proof.
    start_function.
    destruct h as ((p, i), g).
    viewshift_SEP 0 (|> inv_for_lock p R).
    { go_lower; simpl; Intros.
      apply cinv_cancel; auto. }
    unfold inv_for_lock.
    rewrite (later_exp' _ true); Intros b.
    simpl.
    assert_PROP (is_pointer_or_null p) by entailer!.
    forward_call (p).
    - Exists (Val.of_bool b); cancel.
    - destruct b; [entailer!|].
      + apply andp_left2; auto.
      + eapply derives_trans, FF_left.
        entailer!.
        eapply derives_trans, modus_ponens_wand.
        rewrite (sepcon_comm R).
        apply sepcon_derives, andp_left1; apply derives_refl.
  Qed.

  Lemma body_release: semax_body Vprog Gprog f_release release_spec.
  Proof.
    start_function.
    forward_call (ptr_of h, vint 0, @Ensembles.Full_set invariants.iname, @Ensembles.Empty_set invariants.iname, Q).
    - simpl; unfold atomic_lock_inv; destruct h as ((p, i), g); Intros.
      subst Frame; instantiate (1 := []); simpl; cancel.
      rewrite cinvariant_dup at 1.
      sep_apply (cinv_open Ensembles.Full_set); auto.
      repeat sep_apply fupd_frame_r; apply fupd_elim.
      rewrite prop_true_andp by auto.
      sep_apply (modus_ponens_wand (cinvariant i g (inv_for_lock p R) * cinv_own g sh * P)).
      unfold inv_for_lock at 1.
      rewrite (later_exp' _ true); Intros b; destruct b.
      + rewrite sepcon_emp, !sepcon_assoc; sep_eapply fupd_timeless; auto; repeat sep_eapply fupd_frame_r; apply fupd_elim.
        sep_apply atomic_int_at__.
        eapply derives_trans, fupd_mask_intro_all; rewrite <- wand_sepcon_adjoint.
        Exists Ews; simpl; entailer!.
        rewrite <- wand_sepcon_adjoint.
        sep_apply fupd_frame_l; repeat sep_apply fupd_frame_r; apply fupd_elim.
        unfold ptr_of; sep_apply (modus_ponens_wand' (R * atomic_int_at Ews (vint 0) p)).
        { unfold inv_for_lock.
          eapply derives_trans, now_later.
          Exists false; cancel. }
        repeat sep_apply fupd_frame_r; apply fupd_mono; cancel.
        apply andp_left2; auto.
      + eapply derives_trans, except_0_fupd; apply orp_right1.
        rewrite sepcon_comm, !sepcon_assoc; eapply derives_trans; [apply sepcon_derives, now_later; apply derives_refl|].
        rewrite <- later_sepcon; apply later_derives.
        sep_apply weak_exclusive_conflict.
        rewrite FF_sepcon; auto.
    - hnf; inversion 1.
    - entailer!.
  Qed.

  Lemma body_acquire: semax_body Vprog Gprog f_acquire acquire_spec.
  Proof.
    start_function; simpl.
    forward.
    forward_loop (PROP ( )
                       LOCAL (temp _b (vint 0); lvar _expected tint v_expected;
                              temp _lock (ptr_of h))
                       SEP (data_at_ Tsh tint v_expected; atomic_lock_inv sh h R)).
    { entailer!. }
    forward.
    forward_call
      (ptr_of h, Tsh, v_expected, (vint 0), (vint 1), @Ensembles.Full_set invariants.iname, @Ensembles.Empty_set invariants.iname,
            fun v':val =>
              atomic_lock_inv sh h R * if (eq_dec v' (vint 0)) then |> R else emp).
    - unfold atomic_lock_inv; destruct h as ((p, i), g); Intros.
      subst Frame; instantiate (1 := []); simpl fold_right_sepcon; cancel.
      rewrite cinvariant_dup at 1.
      sep_apply (cinv_open Ensembles.Full_set); auto.
      repeat sep_apply fupd_frame_r; apply fupd_elim.
      unfold inv_for_lock at 1.
      rewrite (later_exp' _ true); Intros b.
      rewrite later_sepcon; sep_eapply fupd_timeless; auto; repeat sep_eapply fupd_frame_r; apply fupd_elim.
      eapply derives_trans, fupd_mask_intro_all; rewrite <- wand_sepcon_adjoint.
      Exists Ews (Val.of_bool b); simpl; entailer!.
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
      + forward. simpl lock_specs.lock_inv; entailer!.
      + forward. simpl lock_specs.lock_inv; entailer!.
  Qed.

End PROOFS.

(* freelock and release specialized for self_part *)
Program Definition freelock_spec_self :=
  TYPE (ProdType (ConstType _) Mpred)
  WITH sh1 : _, sh2 : _, h : _, R : _
  PRE [ tptr t_lock ]
     PROP (sh1 <> Share.bot; sh2 <> Share.bot; sepalg.join sh1 sh2 Tsh)
     PARAMS (ptr_of h)
     SEP (weak_exclusive_mpred R && emp; lock_inv sh1 h (self_part sh2 h * R); self_part sh2 h; R)
  POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP (R).
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((?, ?), ?), ?); simpl.
  unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; do 3 f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  f_equal.
  { rewrite !approx_andp; f_equal.
    apply exclusive_mpred_super_non_expansive. }
  setoid_rewrite (@lock_inv_super_non_expansive atomic_impl); do 2 f_equal.
  rewrite !approx_sepcon, approx_idem; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((?, ?), ?), ?); simpl.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  reflexivity.
Qed.

Program Definition release_spec_self :=
  TYPE (ProdType (ConstType _) Mpred)
  WITH sh : _, h : _, R : _
  PRE [ tptr t_lock ]
     PROP (sh <> Share.bot)
     PARAMS (ptr_of h)
     SEP (lock_inv sh h (self_part sh h * R); R)
  POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP ().
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((?, ?), ?); simpl.
  unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; do 3 f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  f_equal.
  setoid_rewrite (@lock_inv_super_non_expansive atomic_impl); do 2 f_equal.
  rewrite !approx_sepcon, approx_idem; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((?, ?), ?); simpl.
  reflexivity.
Qed.

#[export] Hint Resolve self_part_exclusive : core.

Lemma release_self : funspec_sub lock_specs.release_spec release_spec_self.
Proof.
  unfold funspec_sub; simpl.
  split; auto; intros ? ((sh, h), R) ?; Intros.
  eapply derives_trans, fupd_intro.
  Exists (nil : list Type) (sh, h, self_part sh h * R, R, emp) emp; entailer!.
  { intros; unfold PROPx, LOCALx, SEPx; simpl; entailer!. }
  unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; entailer!.
  rewrite <- emp_sepcon at 1; apply sepcon_derives.
  - apply andp_right; auto; eapply derives_trans, exclusive_weak_exclusive; auto.
    apply exclusive_sepcon1; auto.
  - rewrite <- wand_sepcon_adjoint, emp_sepcon; cancel.
    unfold atomic_lock_inv, self_part; destruct h as ((?, ?), ?); Intros; cancel.
    apply inv_dealloc.
Qed.

Lemma freelock_self : funspec_sub lock_specs.freelock_spec freelock_spec_self.
Proof.
  unfold funspec_sub; simpl.
  split; auto; intros ? (((sh1, sh2), h), R) ?; Intros.
  eapply derives_trans, fupd_intro.
  Exists (nil : list Type) (h, self_part sh2 h * R, R) emp; entailer!.
  unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl.
  set (P := _ * _); entailer!; subst P.
  rewrite sepcon_emp, <- (sepcon_assoc _ _ R); setoid_rewrite self_part_eq; auto.
  erewrite lock_inv_share_join by eauto; simpl; cancel.
  apply andp_right, andp_left2; auto.
  rewrite <- wand_sepcon_adjoint.
  sep_apply weak_exclusive_conflict.
  rewrite FF_sepcon; auto.
Qed.

Definition selflock R sh h := self_part sh h * R.

Opaque t_lock.
Opaque lock_handle.
Opaque ptr_of.
Opaque lock_inv.
Opaque self_part.
Arguments ptr_of : simpl never.
Arguments lock_inv : simpl never.
