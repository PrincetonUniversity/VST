Require Export iris_ora.logic.cancelable_invariants.
Require Import VST.concurrency.conclib.
Require Import VST.floyd.library.
Require Import VST.atomics.SC_atomics.
Require Import VST.concurrency.lock_specs.
Require Import VST.concurrency.threads.

Section mpred.

Context `{!VSTGS OK_ty Σ, !cinvG Σ, atom_impl : !atomic_int_impl (Tstruct _atom_int noattr)}.

(* add these to atomic_int_impl? *)
Axiom atomic_int_isptr : forall sh v p, atomic_int_at sh v p ⊢ ⌜isptr p⌝.
#[local] Hint Resolve atomic_int_isptr : saturate_local.
Axiom atomic_int_timeless : forall sh v p, Timeless (atomic_int_at sh v p).
#[export] Existing Instance atomic_int_timeless.

#[global] Opaque atomic_int_at.

Section PROOFS.

  #[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
  Definition Vprog : varspecs. mk_varspecs prog. Defined.

  Definition make_atomic_spec := DECLARE _make_atomic make_atomic_spec.
  Definition free_atomic_spec := DECLARE _free_atomic free_atomic_int_spec.
  Definition atom_store_spec := DECLARE _atom_store atomic_store_spec.
  Definition atom_CAS_spec := DECLARE _atom_CAS atomic_CAS_spec.

  Definition inv_for_lock v R := ∃ b, atomic_int_at Ews (Val.of_bool b) v ∗ if b then emp else R.

  #[global] Instance inv_for_lock_nonexpansive : forall v, NonExpansive (inv_for_lock v).
  Proof. solve_proper. Qed.

  Definition atomic_lock_inv sh h R := let '(v, i, g) := h in ⌜isptr v⌝ ∧ cinv i g (inv_for_lock v R) ∗ cinv_own g sh.

  #[export] Program Instance atomic_impl : lock_impl := { t_lock := Tstruct _atom_int noattr; lock_handle := val * namespace * gname;
    ptr_of h := let '(v, i, g) := h in v; lock_inv := atomic_lock_inv }.
  Next Obligation.
  Proof.
    solve_proper.
  Qed.
  Next Obligation.
  Proof.
    unfold atomic_lock_inv.
    intros ?? ((?, ?), ?) ?.
    rewrite /cinv_own own_op; iSplit.
    - iIntros "(($ & $ & $) & (_ & _ & $))".
    - iIntros "(#$ & #$ & $ & $)".
  Qed.
  Next Obligation.
  Proof.
    intros ? ((?, ?), ?) ?.
    unfold atomic_lock_inv; entailer!.
  Qed.

  (* We can use self_part sh h ∗ R instead of selflock sh h R. *)
  Definition self_part sh (h : lock_handle) := let '(v, i, g) := h in cinv_own g sh.

(*  Lemma self_part_exclusive : forall sh h, sh <> Share.bot -> exclusive_mpred (self_part sh h).
  Proof.
    intros; unfold exclusive_mpred, self_part; destruct h as ((?, ?), ?).
    unfold cinv_own; rewrite own_op'; Intros ?.
    apply sepalg.join_self, identity_share_bot in H0; contradiction.
  Qed.*)

  Lemma self_part_eq : forall sh1 sh2 h R, lock_inv sh1 h (self_part sh2 h ∗ R) ∗ self_part sh2 h ⊣⊢
    lock_inv sh1 h (self_part sh2 h ∗ R) ∗ lock_inv sh2 h (self_part sh2 h ∗ R).
  Proof.
    intros.
    simpl; unfold atomic_lock_inv; destruct h as ((?, ?), ?).
    iSplit.
    - iIntros "((#$ & #$ & $) & $)".
    - iIntros "(($ & $ & $) & (_ & _ & $))".
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
    Exists (p, i, g); unfold atomic_lock_inv; entailer!.
  Qed.

  Lemma body_freelock: semax_body Vprog Gprog f_freelock freelock_spec.
  Proof.
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
    - gather_SEP 0 1 2 3.
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

  Lemma body_release: semax_body Vprog Gprog f_release release_spec.
  Proof.
    start_function.
    forward_call (ptr_of h, vint 0, ⊤ : coPset, ∅ : coPset, Q).
    - destruct h as ((p, i), g); simpl; Intros.
      subst Frame; instantiate (1 := []); simpl; cancel.
      iIntros "(HR & #I & ? & P & HQ)".
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

  Lemma body_acquire: semax_body Vprog Gprog f_acquire acquire_spec.
  Proof.
    start_function.
    forward.
    forward_loop (PROP ( )
                       LOCAL (temp _b (vint 0); lvar _expected tint v_expected;
                              temp _lock (ptr_of h))
                       SEP (data_at_ Tsh tint v_expected; atomic_lock_inv sh h R)).
    { entailer!. }
    forward.
    forward_call
      (ptr_of h, Tsh, v_expected, (vint 0), (vint 1), ⊤ : coPset, ∅ : coPset,
            fun v':val =>
              atomic_lock_inv sh h R ∗ if (eq_dec v' (vint 0)) then ▷ R else emp).
    - unfold atomic_lock_inv; destruct h as ((p, i), g); Intros.
      subst Frame; instantiate (1 := []); simpl fold_right_sepcon; cancel.
      iIntros "(#I & ?)".
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
  Qed.

End PROOFS.

Opaque lock_inv.

(* freelock and release specialized for self_part *)
Program Definition freelock_spec_self :=
  TYPE (ProdType (ConstType _) Mpred)
  WITH sh1 : _, sh2 : _, h : _, R : _
  PRE [ tptr t_lock ]
     PROP (sh1 ⋅ sh2 = 1%Qp)
     PARAMS (ptr_of h)
     SEP (lock_inv sh1 h (self_part sh2 h ∗ R); self_part sh2 h)
  POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP ().
Next Obligation.
Proof.
  intros ? (((?, ?), ?), ?) (((?, ?), ?), ?) ([=] & HR) ?; simpl in *; subst.
  by repeat f_equiv.
Qed.
Next Obligation.
Proof.
  intros ? (((?, ?), ?), ?) (((?, ?), ?), ?) ([=] & HR) ?; simpl in *; subst.
  by repeat f_equiv.
Qed.

Program Definition release_spec_self :=
  TYPE (ProdType (ConstType _) Mpred)
  WITH sh : _, h : _, R : _
  PRE [ tptr t_lock ]
     PROP ()
     PARAMS (ptr_of h)
     SEP (<affine> (R ∗ R -∗ False); lock_inv sh h (self_part sh h ∗ R); R)
  POST [ tvoid ]
     PROP ()
     LOCAL ()
     SEP ().
Next Obligation.
Proof.
  intros ? ((?, ?), ?) ((?, ?), ?) ([=] & HR) ?; simpl in *; subst.
  by repeat f_equiv.
Qed.
Next Obligation.
Proof.
  intros ? ((?, ?), ?) ((?, ?), ?) ([=] & HR) ?; simpl in *; subst.
  by repeat f_equiv.
Qed.

Transparent lock_inv.

Lemma release_self : funspec_sub lock_specs.release_spec release_spec_self.
Proof.
  unfold funspec_sub; simpl.
  split; first done; intros ((sh, h), R) ?; Intros.
  iIntros "(? & ? & H) !>"; iExists (sh, h, self_part sh h ∗ R, R, emp), emp.
  iSplit.
  - repeat (iSplit; first done).
    rewrite /SEPx /= /LOCALx /argsassert2assert /=; monPred.unseal.
    repeat (iSplit; first done).
    iDestruct "H" as "(? & HR & ? & ? & _)"; iFrame.
    iSplitL "HR".
    + iIntros "!> ((? & ?) & (? & ?))".
      rewrite bi.affinely_elim; iApply ("HR" with "[$]").
    + iSplit; first done; iSplit; last done.
      destruct h as ((?, ?), ?); iIntros "((% & (? & $)) & $)".
  - iPureIntro; intros.
    unfold PROPx, LOCALx, SEPx; simpl; entailer!.
Qed.

Lemma freelock_self : funspec_sub lock_specs.freelock_spec freelock_spec_self.
Proof.
  unfold funspec_sub; simpl.
  split; first done; intros (((sh1, sh2), h), R) ?; Intros.
  iIntros "((%Hsh & _) & ? & H) !>"; iExists (h, self_part sh2 h ∗ R, emp), emp.
  iSplit.
  - repeat (iSplit; first done).
    rewrite /SEPx /= /LOCALx /argsassert2assert /=; monPred.unseal.
    repeat (iSplit; first done).
    iDestruct "H" as "(? & p & self & _)"; iFrame.
    iCombine "p self" as "p"; rewrite self_part_eq lock_inv_share_join Hsh; iFrame.
    iSplit; first done; iSplit; last done.
    iIntros "!> (_ & p & self & ?)".
    iCombine "p self" as "p"; rewrite self_part_eq lock_inv_share_join.
    destruct h as ((?, ?), ?); simpl.
    iDestruct "p" as "(_ & _ & ? & ?)"; iApply (cinv_own_1_l with "[$] [$]").
  - iPureIntro; intros.
    unfold PROPx, LOCALx, SEPx; simpl; entailer!.
Qed.

Definition selflock R sh h := self_part sh h ∗ R.

End mpred.

#[export] Hint Resolve atomic_int_isptr : saturate_local.

Opaque t_lock.
Opaque lock_handle.
Opaque ptr_of.
Opaque lock_inv.
Opaque self_part.
Arguments ptr_of : simpl never.
Arguments lock_inv : simpl never.
