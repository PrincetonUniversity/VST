Require Import VST.veric.rmaps.
Require Import VST.concurrency.conclib.
Require Import VST.concurrency.ghosts.
Require Import VST.concurrency.cancelable_invariants.
Require Import VST.floyd.library.
Require Import VST.atomics.SC_atomics.
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

  Definition make_atomic_spec :=
    DECLARE _make_atomic (make_atomic_spec atomic_int atomic_int_at).
  Definition free_atomic_spec :=
    DECLARE _free_atomic (free_atomic_int_spec atomic_int atomic_int_at).
  Definition atom_store_spec :=
    DECLARE _atom_store (atomic_store_spec atomic_int atomic_int_at).
  Definition atom_CAS_spec :=
    DECLARE _atom_CAS (atomic_CAS_spec atomic_int atomic_int_at).

  Definition inv_for_lock v R := EX b, atomic_int_at Ews (Val.of_bool b) v * if b then emp else R.

  Definition lock_inv sh i g v R := cinvariant i g (inv_for_lock v R) * cinv_own g sh.

  Lemma lock_inv_share_join : forall sh1 sh2 sh3 i g v R, sepalg.join sh1 sh2 sh3 ->
    lock_inv sh1 i g v R * lock_inv sh2 i g v R = lock_inv sh3 i g v R.
  Proof.
    intros; unfold lock_inv, cinvariant.
    rewrite <- !sepcon_assoc, (sepcon_comm (_ * cinv_own _ _)), !sepcon_assoc.
    unfold cinv_own at 3 4; erewrite <- own_op by eauto.
    rewrite <- sepcon_assoc; f_equal.
    symmetry; apply invariants.invariant_dup.
  Qed.

  Lemma lock_inv_super_non_expansive : forall sh i g v R n,
    compcert_rmaps.RML.R.approx n (lock_inv sh i g v R) = compcert_rmaps.RML.R.approx n (lock_inv sh i g v (compcert_rmaps.RML.R.approx n R)).
  Proof.
    intros; unfold lock_inv.
    rewrite !approx_sepcon; f_equal.
    rewrite cinvariant_super_non_expansive; setoid_rewrite cinvariant_super_non_expansive at 2; do 2 f_equal.
    rewrite !approx_exp; f_equal; extensionality.
    rewrite !approx_sepcon; f_equal.
    destruct x; auto.
    rewrite approx_idem; auto.
  Qed.

  Program Definition makelock_spec :=
    DECLARE _makelock
    TYPE (ProdType (ConstType globals) Mpred) WITH gv: globals, R : mpred
    PRE [ ]
       PROP ()
       PARAMS () GLOBALS (gv)
       SEP (mem_mgr gv)
    POST [ tptr t_lock ] EX p i g,
       PROP ()
       RETURN (p)
       SEP (mem_mgr gv; lock_inv Tsh i g p R).
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
    rewrite !approx_exp; f_equal; extensionality.
    rewrite !approx_exp; f_equal; extensionality.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; do 2 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    f_equal; apply lock_inv_super_non_expansive.
  Qed.

  Program Definition freelock_spec :=
    DECLARE _freelock
    TYPE (ProdType (ConstType _) Mpred)
    WITH i : _, g : _, p : val, R : mpred
    PRE [ tptr t_lock ]
     PROP ()
     PARAMS (p)
     SEP (weak_exclusive_mpred R && emp; lock_inv Tsh i g p R; R)
   POST[ tvoid ]
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
    { apply (nonexpansive_super_non_expansive (fun R => weak_exclusive_mpred R && emp))%logic.
      apply (conj_nonexpansive (fun R => weak_exclusive_mpred R)%logic).
      - apply exclusive_mpred_nonexpansive.
      - apply const_nonexpansive. }
    f_equal; apply lock_inv_super_non_expansive.
  Qed.
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as (((?, ?), ?), ?); simpl.
    unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    reflexivity.
  Qed.

  (* Do we need mem_mgr? *)
  Program Definition acquire_spec :=
    DECLARE _acquire
    TYPE (ProdType (ConstType _) Mpred)
    WITH gv : globals, sh : _, i : _, g : _, p : _, R : mpred
    PRE [ tptr t_lock ]
       PROP (readable_share sh)
       PARAMS (p) GLOBALS (gv)
       SEP (mem_mgr gv; lock_inv sh i g p R)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (mem_mgr gv; lock_inv sh i g p R; R).
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as (((((?, ?), ?), ?), ?), ?); simpl.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; do 3 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    f_equal; apply lock_inv_super_non_expansive.
  Qed.
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as (((((?, ?), ?), ?), ?), ?); simpl.
    unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    do 2 f_equal. apply lock_inv_super_non_expansive.
  Qed.

  Program Definition release_spec :=
    DECLARE _release
    TYPE (ProdType (ConstType _) Mpred)
    WITH gv : globals, sh : _, i : _, g : _, p : _, R : mpred
    PRE [ tptr t_lock ]
       PROP (readable_share sh)
       PARAMS (p) GLOBALS (gv)
       SEP (mem_mgr gv; weak_exclusive_mpred R && emp; lock_inv sh i g p R; R)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (mem_mgr gv; lock_inv sh i g p R).
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as (((((?, ?), ?), ?), ?), ?); simpl.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; do 3 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    do 2 f_equal.
    { apply (nonexpansive_super_non_expansive (fun R => weak_exclusive_mpred R && emp))%logic.
      apply (conj_nonexpansive (fun R => weak_exclusive_mpred R)%logic).
      - apply exclusive_mpred_nonexpansive.
      - apply const_nonexpansive. }
    f_equal; apply lock_inv_super_non_expansive.
  Qed.
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as (((((?, ?), ?), ?), ?), ?); simpl.
    unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    f_equal. apply lock_inv_super_non_expansive.
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
    viewshift_SEP 0 (EX i g, lock_inv Tsh i g p R).
    { go_lower.
      unfold lock_inv.
      eapply derives_trans, cinv_alloc.
      unfold inv_for_lock.
      eapply derives_trans, now_later.
      Exists true; cancel. }
    simpl.
    forward.
    Exists p i g; entailer!.
  Qed.

  Lemma body_freelock: semax_body Vprog Gprog f_freelock freelock_spec.
  Proof.
    start_function.
    viewshift_SEP 1 (|> inv_for_lock p R).
    { go_lower.
      unfold lock_inv.
      apply cinv_cancel. }
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
    forward_call (p, (vint 0), @Ensembles.Full_set invariants.iname, @Ensembles.Empty_set invariants.iname, lock_inv sh i g p R).
    - unfold lock_inv.
      subst Frame; instantiate (1 := [mem_mgr gv]); simpl fold_right_sepcon; cancel.
(*      iIntros ">AS".
      iDestruct "AS" as (x) "[a [_ H]]".
      iExists Ews. iModIntro. iSplitL "a".
      + iSplit.
        * iPureIntro. apply writable_Ews.
        * iApply atomic_int_at__. iAssumption.
      + iIntros "AA".
        iPoseProof (sepcon_emp (atomic_int_at Ews (vint 0) p)) as "HA".
        iSpecialize ("HA" with "AA"). iMod ("H" $! tt with "HA"). auto.*) admit.
    - hnf; inversion 1.
    - entailer!.
  Admitted.

  Lemma body_acquire: semax_body Vprog Gprog f_acquire acquire_spec.
  Proof.
    start_function.
    forward.
    forward_loop (PROP ( )
                       LOCAL (temp _b (vint 0); lvar _expected tint v_expected;
                              gvars gv; temp _lock p)
                       SEP (data_at_ Tsh tint v_expected; mem_mgr gv; lock_inv sh i g p R)).
    - entailer!.
    - forward.
      forward_call
        (p , Tsh, v_expected, (vint 0), (vint 1), @Ensembles.Full_set invariants.iname, @Ensembles.Empty_set invariants.iname,
              fun v':val =>
                lock_inv sh i g p R * if (eq_dec v' (vint 0)) then R else emp).
      + subst Frame; instantiate (1 := [mem_mgr gv]); simpl fold_right_sepcon; cancel.
        (*iIntros ">AS". iExists Ews.
        iDestruct "AS" as (x) "[[a | a] H]".
        * iDestruct "H" as "[_ H]". iDestruct "a" as (a) "b".
          iExists (vint 0). iModIntro. iSplitL "b".
          -- iSplit; auto.
          -- iSpecialize ("H" $! tt). iIntros "AA". iApply "H".
             destruct (eq_dec (vint 0) (vint 0)). 2: exfalso; now apply n.
             iSplit; [iSplit|]; auto.
        * iExists (vint 1). iModIntro. destruct (eq_dec (vint 1) (vint 0)).
          1: inversion e. rewrite sepcon_andp_prop'. iSplit.
          -- iPureIntro. apply writable_Ews.
          -- iDestruct "a" as (Hx) "a". iSplitL "a"; first auto. iIntros "AS".
             iMod ("H" with "[AS]").
             { iRight; iFrame; auto. }
             iFrame; auto.*) admit.
      + hnf; inversion 1.
      + Intros r. forward_if.
        * if_tac; try discriminate. forward. entailer!.
        * if_tac; try contradiction. forward. entailer!.
  Admitted.

End PROOFS.
