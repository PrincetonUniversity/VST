Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library. (*for body_lemma_of_funspec *)
Require Import VSTlib.locks.
Require Import VSTlib.spec_locks.
Require Import VSTlib.spec_malloc.
Require Import VSTlib.spec_SC_atomics.
Require Import VSTlib.verif_SC_atomics VSTlib.verif_malloc.
Require Import VST.veric.rmaps.
Require Import VST.concurrency.conclib.
Require Import VST.concurrency.ghosts. (* why does this have locks in it? *)
Require Import VST.concurrency.cancelable_invariants.

#[global] Opaque VSTlib.verif_SC_atomics.M.

#[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition inv_for_lock' v R := 
  EX b, atomic_int_at Ews (Val.of_bool b) v * if b then emp else R.

Lemma inv_for_lock_nonexpansive' : forall v, nonexpansive (inv_for_lock' v).
  Proof.
    intros.
    apply @exists_nonexpansive; intros.
    apply sepcon_nonexpansive; [apply const_nonexpansive|].
    destruct x; [apply const_nonexpansive | apply identity_nonexpansive].
  Qed.

#[export] Program Instance M : lockAPD := {
  inv_for_lock := fun v R => EX b, atomic_int_at Ews (Val.of_bool b) v * if b then emp else R
}.
Next Obligation. (*inv_for_lock_nonexpansive *)
  Proof.
    intros.
    apply @exists_nonexpansive; intros.
    apply sepcon_nonexpansive; [apply const_nonexpansive|].
    destruct x; [apply const_nonexpansive | apply identity_nonexpansive].
  Qed.

  Definition makelock_spec := DECLARE _makelock (@spec_locks.makelock_spec verif_malloc.M M).
  Definition freelock_spec := DECLARE _freelock spec_locks.freelock_spec.
  Definition acquire_spec := DECLARE _acquire spec_locks.acquire_spec.
  Definition release_spec := DECLARE _release spec_locks.release_spec.

Definition lockImports : funspecs :=
  (* AtomicsASI ++ MallocASI    (* should be able to write this *) *)
  (* Bug? must list exactly and only the actual imports used: *)
  [(SC_atomics_extern._make_atomic, make_atomic_spec);
 (SC_atomics_extern._free_atomic, free_atomic_int_spec);
 (SC_atomics_extern._atom_store, atomic_store_spec);
 (SC_atomics_extern._atom_CAS, atomic_CAS_spec)].

Definition Gprog := lockImports ++ LockASI.

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
    simpl; Exists (p, i, g); unfold lock_inv; entailer!. apply derives_refl.
  Qed.

  #[local] Hint Resolve Ensembles.Full_intro : core.

  Lemma body_freelock: semax_body Vprog Gprog f_freelock freelock_spec.
  Proof.
    start_function.
    destruct h as ((p, i), g); simpl; Intros.
    gather_SEP (cinvariant _ _ _) (cinv_own _ _); viewshift_SEP 0 (cinvariant i g (inv_for_lock p R) * |> inv_for_lock p R).
    { go_lower; simpl; Intros.
      rewrite cinvariant_dup at 1; unfold cinvariant at 1; sep_apply (inv_open Ensembles.Full_set); auto.
      eapply derives_trans, fupd_elim; [apply fupd_frame_r|].
      rewrite later_orp, !distrib_orp_sepcon; apply orp_left.
      - sep_apply (modus_ponens_wand' (cinv_own g Tsh)).
        { apply orp_right2, now_later. }
        sep_apply fupd_frame_r; rewrite emp_sepcon.
        sep_apply fupd_frame_r; rewrite sepcon_comm; apply derives_refl.
      - eapply derives_trans, except_0_fupd.
        apply orp_right1.
        rewrite sepcon_assoc; eapply derives_trans; [apply sepcon_derives, now_later; apply derives_refl|].
        rewrite <- later_sepcon; apply later_derives.
        sep_apply cinv_own_excl.
        rewrite FF_sepcon; auto. }
    unfold inv_for_lock at 2. unfold M at 2.
    rewrite (later_exp' _ true); Intros b.
    destruct b.
    - assert_PROP (is_pointer_or_null p) by entailer!.
      forward_call (p).
      { Exists (Val.of_bool true); cancel. }
      entailer!.
      rewrite <- emp_sepcon; apply sepcon_derives, andp_left2, derives_refl.
      apply inv_dealloc.
    - gather_SEP 0 1 2 3.
      viewshift_SEP 0 FF.
      go_lower.
      rewrite cinvariant_dup at 1.
      unfold cinvariant at 1; sep_apply (inv_open Ensembles.Full_set); auto.
      eapply derives_trans, fupd_elim; [apply fupd_frame_r|].
      rewrite <- !sepcon_assoc, (sepcon_comm _ (|> _)), <- !sepcon_assoc.
      rewrite 3sepcon_assoc; eapply derives_trans; [apply sepcon_derives, derives_refl|].
      { rewrite <- later_sepcon; apply later_derives.
        rewrite distrib_orp_sepcon2; apply orp_left, derives_refl.
        unfold inv_for_lock, M; Intros b.
        sep_apply atomic_int_conflict; auto.
        rewrite FF_sepcon; apply FF_left. }
      rewrite <- !sepcon_assoc, (sepcon_comm _ (_ -* _)).
      rewrite !later_sepcon, <- !sepcon_assoc, 4sepcon_assoc.
      eapply derives_trans; [apply sepcon_derives; [apply derives_refl|]|].
      rewrite <- !sepcon_assoc; eapply derives_trans, modus_ponens_wand.
      eapply sepcon_derives, derives_trans; [|apply now_later | rewrite later_andp, later_wand; apply andp_left1, derives_refl].
      rewrite !later_sepcon; entailer!.
      apply now_later.
      { rewrite sepcon_assoc, <- later_sepcon, sepcon_FF.
        eapply derives_trans; [apply sepcon_derives, derives_refl; apply now_later|].
        rewrite <- later_sepcon, sepcon_FF.
        eapply derives_trans, except_0_fupd; apply orp_right1; auto. }
      { eapply semax_pre, semax_ff; entailer!. }
  Qed.

Opaque inv_for_lock.

  Lemma body_release: semax_body Vprog Gprog f_release release_spec.
  Proof.
    start_function.
    forward_call (ptr_of h, vint 0, @Ensembles.Full_set invariants.iname, @Ensembles.Empty_set invariants.iname, Q).
    - simpl; unfold lock_inv; destruct h as ((p, i), g); Intros.
      subst Frame; instantiate (1 := []); simpl; cancel.
      rewrite cinvariant_dup at 1.
      sep_apply (cinv_open Ensembles.Full_set); auto.
      repeat sep_apply fupd_frame_r; apply fupd_elim.
      rewrite prop_true_andp by auto.
      sep_apply (modus_ponens_wand (cinvariant i g (inv_for_lock p R) * cinv_own g sh * P)).
      unfold inv_for_lock at 1. unfold M at 1.
      rewrite (later_exp' _ true); Intros b; destruct b.
      + rewrite sepcon_emp, !sepcon_assoc; sep_eapply fupd_timeless; auto; repeat sep_eapply fupd_frame_r; apply fupd_elim.
        sep_apply atomic_int_at__.
        eapply derives_trans, fupd_mask_intro_all; rewrite <- wand_sepcon_adjoint.
        Exists Ews; simpl; entailer!.
        rewrite <- wand_sepcon_adjoint.
        sep_apply fupd_frame_l; repeat sep_apply fupd_frame_r; apply fupd_elim.
        unfold ptr_of; sep_apply (modus_ponens_wand' (R * atomic_int_at Ews (vint 0) p)).
        { unfold inv_for_lock at 1. unfold M.
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
                       SEP (data_at_ Tsh tint v_expected; lock_inv sh h R)).
    { entailer!. }
    forward.
    forward_call
      (ptr_of h, Tsh, v_expected, (vint 0), (vint 1), @Ensembles.Full_set invariants.iname, @Ensembles.Empty_set invariants.iname,
            fun v':val =>
              lock_inv sh h R * if (eq_dec v' (vint 0)) then |> R else emp).
    - unfold lock_inv; destruct h as ((p, i), g); Intros.
      subst Frame; instantiate (1 := []); simpl fold_right_sepcon; cancel.
      rewrite cinvariant_dup at 1.
      sep_apply (cinv_open Ensembles.Full_set); auto.
      repeat sep_apply fupd_frame_r; apply fupd_elim.
      unfold inv_for_lock at 1. unfold M at 1.
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
        { unfold inv_for_lock at 1. unfold M at 1.
          eapply derives_trans, now_later.
          Exists true; cancel. }
        repeat sep_apply fupd_frame_r; apply fupd_mono; cancel.
      + rewrite !if_true by auto.
        sep_apply (modus_ponens_wand' (atomic_int_at Ews (vint 1) p)).
        { unfold inv_for_lock at 1. unfold M at 1.
          eapply derives_trans, now_later.
          Exists true; cancel. }
        repeat sep_apply fupd_frame_r; apply fupd_mono; cancel.
    - hnf; inversion 1.
    - Intros r. if_tac; forward_if; try discriminate; try contradiction.
      + forward. simpl lock_specs.lock_inv; entailer!.
      + forward. simpl lock_specs.lock_inv; entailer!.
Unshelve.
apply Build_change_composite_env with (coeq := Maps.PTree.empty bool).
intros. inv H1. intros. unfold cenv_cs; simpl. rewrite !Maps.PTree.gempty.
split; intros [? ?]; discriminate.
  Qed.

#[global] Opaque M.

#[local] Existing Instance NullExtension.Espec.  (* FIXME *)

Definition LockVSU: VSU nil lockImports ltac:(QPprog prog) LockASI emp.
  Proof. 
    mkVSU prog LockASI.
    - solve_SF_internal body_makelock.
    - solve_SF_internal body_freelock.
    - solve_SF_internal body_acquire.
    - solve_SF_internal body_release.
  Qed.
