Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.floyd.library. (*for body_lemma_of_funspec *)
Require Import VSTlib.locks.
Require Import VSTlib.spec_locks.
Require Import VSTlib.spec_malloc.
Require Import VSTlib.spec_SC_atomics.
Require Import VSTlib.verif_SC_atomics VSTlib.verif_malloc.
Require Import VST.concurrency.conclib.
Require Import iris_ora.logic.cancelable_invariants.

#[global] Opaque VSTlib.verif_SC_atomics.M.

#[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.


Section mpred.

Context `{!VSTGS OK_ty Σ, !cinvG Σ, atom_impl : !atomic_int_impl (Tstruct _atom_int noattr)}.


#[export] Program Instance M : lockAPD := {
  inv_for_lock := fun v R => ∃ b, atomic_int_at Ews (Val.of_bool b) v ∗ if b then emp else R
}.
Next Obligation. (*inv_for_lock_nonexpansive *)
  Proof. solve_proper. Qed.

  Definition makelock_spec := DECLARE _makelock spec_locks.makelock_spec.
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
  (* the following line should not be necessary;
    start_function1 should do a better job unfolding,
    but currently it's blocked on spec-definitions that
    have implicit arguments. *)
  unfold makelock_spec, spec_locks.makelock_spec.
    start_function.
    forward_call (vint 1).
    Intros p.
    viewshift_SEP 0 (∃ i g, lock_inv 1 (p, i, g) (R (p, i, g))).
    { go_lowerx.
      iIntros "(? & _)".
      iDestruct (atomic_int_isptr with "[$]") as "#$".
      iMod (cinv_alloc_strong (λ _, True%type) _ (nroot .@ "lock")) as (?) "(_ & ? & inv)".
      { apply pred_infinite_True. }
      iExists _, _; iFrame; iApply "inv".
      rewrite /inv_for_lock.
      iExists true; auto. }
    forward.
    unfold lock_inv; simpl.
    Exists (p, i, g); unfold lock_inv; entailer!!.
  Qed.

  Lemma body_freelock: semax_body Vprog Gprog f_freelock freelock_spec.
  Proof.
  (* the following line should not be necessary;
    start_function1 should do a better job unfolding,
    but currently it's blocked on spec-definitions that
    have implicit arguments. *)
  unfold freelock_spec, spec_locks.freelock_spec.
    start_function.
    destruct h as ((p, i), g); simpl; Intros.
    gather_SEP (cinv _ _ _) (cinv_own _ _); viewshift_SEP 0 (cinv i g (inv_for_lock p R) ∗ ▷ inv_for_lock p R).
    { go_lowerx.
      iIntros "((#$ & ?) & _)".
      iMod (cinv_cancel with "[$] [$]") as "$"; done. }
    unfold inv_for_lock at 2.
    rewrite bi.later_exist; Intros b.
    destruct b.
    - forward_call (p).
      { Exists (Val.of_bool true); cancel. }
      entailer!.
      by iIntros "(_ & _)".
    - gather_SEP (cinv _ _ _) (▷ _) (P) (<affine> _).
      viewshift_SEP 0 (False : mpred).
      go_lowerx.
      iIntros "((#I & (p & R) & P & HR) & _)".
      rewrite {1}/cinv.
      iInv "I" as "[(% & p' & ?) | Hown]".
      { iAssert (▷False) with "[p p']" as ">[]".
        iApply atomic_int_conflict; last iFrame; auto. }
      iAssert (▷ False) with "[-]" as ">[]".
      iNext; rewrite bi.affinely_elim; iDestruct ("HR" with "[$P $R $Hown]") as "[]"; done.
      { eapply semax_pre, semax_ff; go_lower; done. }
  Qed.

Opaque inv_for_lock.

  Lemma body_release: semax_body Vprog Gprog f_release release_spec.
  Proof.
  (* the following line should not be necessary;
    start_function1 should do a better job unfolding,
    but currently it's blocked on spec-definitions that
    have implicit arguments. *)
  unfold release_spec, spec_locks.release_spec.
    start_function.
    forward_call (ptr_of h, vint 0, ⊤ : coPset, ∅ : coPset, Q).
    - destruct h as ((p, i), g); simpl; Intros.
      subst Frame; instantiate (1 := []); simpl; cancel.
      iIntros "(HR & #I & ? & P & HQ)".
 (* the next line fails for some reason 
      iInv i as "((% & >p & ?) & Hown)" "Hclose".
      destruct b.
      + iExists Ews; rewrite (bi.pure_True (writable_share _)) //.
        rewrite atomic_int_at__; iFrame.
        iApply fupd_mask_intro; first set_solver.
        iIntros "Hmask p".
        iDestruct ("HQ" with "[$Hown $P]") as "($ & ?)"; first auto.
        iMod "Hmask"; iApply "Hclose".
        iExists false; iFrame.
      + iDestruct ("HQ" with "[$Hown $P]") as "(? & ?)"; first auto.
        iAssert (▷ False) with "[-]" as ">[]".
        rewrite bi.affinely_elim; iNext; iApply ("HR" with "[$]").
    - entailer!.
  Qed.
*) Admitted.

  Lemma body_acquire: semax_body Vprog Gprog f_acquire acquire_spec.
  Proof.
  (* the following line should not be necessary;
    start_function1 should do a better job unfolding,
    but currently it's blocked on spec-definitions that
    have implicit arguments. *)
  unfold acquire_spec, spec_locks.acquire_spec.
    start_function.
    forward.
    forward_loop (PROP ( )
                       LOCAL (temp _b (vint 0); lvar _expected tint v_expected;
                              temp _lock (ptr_of h))
                       SEP (data_at_ Tsh tint v_expected; lock_inv sh h R)).
    { unfold lock_inv; simpl; entailer!. }
    forward.
    forward_call
      (ptr_of h, Tsh, v_expected, (vint 0), (vint 1), ⊤ : coPset, ∅ : coPset,
            fun v':val =>
              lock_inv sh h R ∗ if (eq_dec v' (vint 0)) then ▷ R else emp).
    - unfold lock_inv; destruct h as ((p, i), g); Intros.
      subst Frame; instantiate (1 := []); simpl fold_right_sepcon; cancel.
      iIntros "(#I & ?)".
 (* the next line fails for some reason 
      iInv "I" as "((% & >? & ?) & ?)" "Hclose".
      iExists Ews, (Val.of_bool b); rewrite (bi.pure_True (writable_share _)) //.
      iFrame.
      iApply fupd_mask_intro; first set_solver.
      iIntros "Hmask p"; iMod "Hmask" as "_".
      destruct b; simpl.
      + iMod ("Hclose" with "[-]"); last auto.
        iExists true; iFrame.
      + iMod ("Hclose" with "[p]"); last by iFrame; auto.
        iExists true; iFrame; auto.
    - Intros r. if_tac; forward_if; try discriminate; try contradiction.
      + forward. simpl lock_inv; entailer!.
      + forward. simpl lock_inv; entailer!.
  Qed. *)
  Admitted.

#[global] Opaque M.

Definition LockVSU `{Espec: ext_spec OK_ty}: VSU nil lockImports ltac:(QPprog prog) LockASI (fun _ => emp).
  Proof. 
    mkVSU prog LockASI.
    - solve_SF_internal body_makelock.
    - solve_SF_internal body_freelock.
    - solve_SF_internal body_acquire.
    - solve_SF_internal body_release.
  Qed.

End mpred.

