Require Import VST.concurrency.conclib.
Require Export VST.concurrency.lock_specs.
Require Import VST.floyd.library.
Require Export VST.atomics.verif_lock.
Require Export VST.atomics.SC_atomics.
Require Export VST.atomics.general_atomics.
Require Import VST.concurrency.threads.

Section PROOFS.

  #[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
  Definition Vprog : varspecs. mk_varspecs prog. Defined.

  Context `{!VSTGS OK_ty Σ, !cinvG Σ, atom_impl : !atomic_int_impl (Tstruct _atom_int noattr)}.

  Definition make_atomic_spec :=
    DECLARE _make_atomic make_atomic_spec.
  Definition free_atomic_spec :=
    DECLARE _free_atomic free_atomic_int_spec.
  Definition atom_store_spec :=
    DECLARE _atom_store atomic_store_spec.
  Definition atom_CAS_spec :=
    DECLARE _atom_CAS atomic_CAS_spec.

  Definition makelock_spec :=
    DECLARE _makelock
    WITH gv: globals
    PRE [ ]
       PROP ()
       PARAMS () GLOBALS (gv)
       SEP (mem_mgr gv)
    POST [ tptr t_lock ] ∃ p,
       PROP ()
       RETURN (p)
       SEP (mem_mgr gv; atomic_int_at Ews (vint 1) p).

  Definition freelock_spec :=
    DECLARE _freelock
    WITH p : val
    PRE [ tptr t_lock ]
     PROP ()
     PARAMS (p)
     SEP (∃ v : val, atomic_int_at Ews v p)
   POST[ tvoid ]
     PROP ()
     LOCAL ()
     SEP ().

  Program Definition release_spec :=
    DECLARE _release
    ATOMIC TYPE (ConstType val) INVS empty
    WITH p
    PRE [ tptr t_lock ]
       PROP ()
       PARAMS (p)
       SEP () | (atomic_int_at Ews (vint 1) p)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP () | (atomic_int_at Ews (vint 0) p).

  Program Definition acquire_spec :=
    DECLARE _acquire
    ATOMIC TYPE (ConstType val) OBJ l INVS empty
    WITH p
    PRE [ tptr t_lock ]
       PROP ()
       PARAMS (p)
       SEP () | (atomic_int_at Ews (Val.of_bool l) p)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP () | (⌜l = false⌝ ∧ atomic_int_at Ews (vint 1) p).

  Definition Gprog : funspecs :=
    ltac:(with_library prog [make_atomic_spec; atom_store_spec; atom_CAS_spec;
                             free_atomic_spec; makelock_spec; freelock_spec;
                             release_spec; acquire_spec]).

  Lemma body_makelock: semax_body Vprog Gprog f_makelock makelock_spec.
  Proof.
    start_function.
    forward_call (vint 1).
    Intros p.
    forward.
    Exists p.
    entailer!.
  Qed.

  Lemma body_freelock: semax_body Vprog Gprog f_freelock freelock_spec.
  Proof.
    start_function.
    Intros v.
    assert_PROP (is_pointer_or_null a) by entailer.
    forward_call.
    - Exists v. cancel.
    - entailer!.
  Qed.

  Lemma body_release: semax_body Vprog Gprog f_release release_spec.
  Proof.
    start_function.
    forward_call (p, (vint 0), top: coPset, empty: coPset, Q).
    - assert (Frame = []); subst Frame; [ reflexivity | clear H].
      simpl fold_right_sepcon. cancel.
      iIntros ">AS".
      iDestruct "AS" as (x) "[a [_ H]]".
      iExists Ews. iModIntro. iSplit; first done. iSplitL "a".
      + iApply atomic_int_at__. iAssumption.
      + iIntros "AA".
        iApply "H"; iFrame.
    - entailer!.
  Qed.

  Lemma body_acquire: semax_body Vprog Gprog f_acquire acquire_spec.
  Proof.
    start_function.
    forward.
    set (AS := atomic_shift _ _ _ _ _).
    forward_loop (PROP ( )
                       LOCAL (temp _b (vint 0); lvar _expected tint v_expected;
                              temp _lock p)
                       SEP (data_at_ Tsh tint v_expected; AS)).
    - entailer!.
    - forward.
      forward_call
        (p, Tsh, v_expected, (vint 0), (vint 1), top : coPset, empty : coPset,
              fun v':val => if (eq_dec v' (vint 0)) then Q else AS).
      + assert (Frame = []); subst Frame; [ reflexivity | clear H].
        simpl fold_right_sepcon. cancel.
        iIntros ">AS !>".
        iDestruct "AS" as (x) "[a H]".
        iExists Ews, (Val.of_bool x); iFrame "a"; iSplit; first done.
        iIntros "a"; destruct x; simpl.
        * iApply "H"; auto.
        * iDestruct "H" as "[_ H]"; iApply ("H" $! tt); iFrame; auto.
      + Intros r. destruct (eq_dec r (vint 0)).
        * forward_if; try discriminate. forward. simpl. entailer!.
        * forward_if; try contradiction. forward. entailer!.
  Qed.

  Program Definition release_spec_nonatomic :=
    WITH p : val
    PRE [ tptr t_lock ]
       PROP ()
       PARAMS (p)
       SEP (atomic_int_at Ews (vint 1) p)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (atomic_int_at Ews (vint 0) p).

  Lemma release_nonatomic: funspec_sub (snd release_spec) release_spec_nonatomic.
  Proof.
    split; first done. intros p ?. simpl in *. Intros.
    unfold rev_curry, tcurry; simpl. iIntros "H !>". iExists (p, atomic_int_at Ews (vint 0) p), emp.
    rewrite bi.emp_sep. iSplit.
    - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; monPred.unseal.
      iDestruct "H" as "(% & % & _ & H & _)".
      do 4 (iSplit; auto).
      unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
      iExists tt; iFrame "H".
      iApply fupd_mask_intro; first done; iIntros "Hclose".
      iSplit; [iIntros "$" | iIntros (_) "[$ _]"]; auto.
    - iPureIntro. intros. Intros. rewrite bi.emp_sep //.
  Qed.



  (* Asymmetric consequence means we can't prove the specs from lock_specs directly,
     but we can wrap a view shift around them. Paradoxically, as shown in verif_lock,
     we would be able to prove lock_specs directly (without using funspec_sub), but
     that conflicts with the "one spec in Gprog" approach. *)

  Definition name_of (h : lock_handle) := let '(v, i, g) := h in i.

  (* caller can request the lock's namespace *)
  Program Definition makelock_spec_inv :=
    TYPE (ProdType (ConstType (globals * namespace)) (ArrowType (ConstType lock_handle) Mpred)) WITH gv: _, N : _, R : _
    PRE [ ]
       PROP ()
       PARAMS () GLOBALS (gv)
       SEP (mem_mgr gv)
    POST [ tptr t_lock ] (* asymmetric consequence makes this messy *) ∃ v,
       PROP ()
       RETURN (v)
       SEP (mem_mgr gv; |={⊤}=> ∃ h, ⌜ptr_of h = v /\ name_of h = N⌝ ∧ lock_inv 1 h (R h)).

  (* These lemmas can be used to attach an invariant to an existing lock. *)
  Lemma make_lock_inv_1 : forall v N (R : lock_handle -> mpred), atomic_int_at Ews (vint 1) v ⊢ |={⊤}=> (∃ h, ⌜ptr_of h = v /\ name_of h = N⌝ ∧ lock_inv 1 h (R h)).
  Proof.
    intros.
    iIntros "a".
    iDestruct (atomic_int_isptr with "a") as %Ha.
    iMod cinv_alloc_strong as (g) "(_ & Hg & Hi)"; first apply pred_infinite_True.
    iExists (v, N, g); unfold lock_inv; simpl; iFrame.
    iMod ("Hi" $! (inv_for_lock v (R (v, N, g))) with "[-]").
    { iExists true; iFrame; done. }
    iFrame; done.
  Qed.

  Lemma make_lock_inv_0_self : forall v N R sh1 sh2, sh1 ⋅ sh2 = 1%Qp ->
    (atomic_int_at Ews (vint 0) v ∗ R) ⊢ |={⊤}=> (∃ h, ⌜ptr_of h = v /\ name_of h = N⌝ ∧ lock_inv sh1 h (R ∗ self_part sh2 h)).
  Proof.
    intros.
    iIntros "[a R]".
    iDestruct (atomic_int_isptr with "a") as %Ha.
    iMod cinv_alloc_strong as (g) "(_ & Hg & Hi)"; first apply pred_infinite_True.
    iExists (v, N, g); unfold lock_inv; simpl.
    rewrite -H; iDestruct "Hg" as "($ & Hg)".
    iMod ("Hi" $! (inv_for_lock v (R ∗ cinv_own g sh2)) with "[-]").
    { iExists false; iFrame; done. }
    iFrame; done.
  Qed.

  Lemma make_lock_inv_0' : forall v N (R : lock_handle -> mpred), (atomic_int_at Ews (vint 0) v ∗ ∀ g, R g) ⊢ |={⊤}=> (∃ h, ⌜ptr_of h = v /\ name_of h = N⌝ ∧ lock_inv 1 h (R h)).
  Proof.
    intros.
    iIntros "[a R]".
    iDestruct (atomic_int_isptr with "a") as %Ha.
    iMod cinv_alloc_strong as (g) "(_ & Hg & Hi)"; first apply pred_infinite_True.
    iExists (v, N, g); unfold lock_inv; simpl; iFrame.
    iMod ("Hi" $! (inv_for_lock v (R (v, N, g))) with "[-]").
    { iExists false; iFrame; done. }
    iFrame; done.
  Qed.

  Lemma make_lock_inv_0 : forall v N R, atomic_int_at Ews (vint 0) v ∗ R ⊢ |={⊤}=> (∃ h, ⌜ptr_of h = v /\ name_of h = N⌝ ∧ lock_inv 1 h R).
  Proof.
    intros.
    rewrite -make_lock_inv_0'.
    by iIntros "($ & $)".
  Qed.

  Lemma makelock_inv: funspec_sub (snd makelock_spec) makelock_spec_inv.
  Proof.
    split; first done. intros ((gv, N), R) ?; simpl in *. Intros.
    iIntros "H !>". iExists gv, emp. rewrite bi.emp_sep. iSplit; auto.
    iPureIntro. intros. Intros. rewrite bi.emp_sep. monPred.unseal. Intros x; Exists x.
    iIntros "(? & $ & $ & ? & _)".
    iSplit; first done.
    rewrite bi.sep_emp; by iApply make_lock_inv_1.
  Qed.

  (* Yet another variant: we only learn the lock invariant after a successful acquire. *)
  Program Definition acquire_spec_inv_atomic1 :=
    ATOMIC TYPE (ConstType val) OBJ R INVS empty
    WITH p
    PRE [ tptr t_lock ]
       PROP ()
       PARAMS (p)
       SEP () | (inv_for_lock p R)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP () | (inv_for_lock p R ∗ R).

  Lemma acquire_inv_atomic: funspec_sub (snd acquire_spec) acquire_spec_inv_atomic1.
  Proof.
    split; first done. intros (p, Q) ?; simpl in *. Intros.
    unfold rev_curry, tcurry; simpl. iIntros "H !>".
    iExists (p, Q), emp; simpl.
    rewrite bi.emp_sep. iSplit.
    - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; monPred.unseal.
      iDestruct "H" as "(% & % & _ & H & _)".
      do 4 (iSplit; auto).
      unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
      iMod "H" as (R) "[H Hclose]".
      unfold inv_for_lock at 1.
      iDestruct "H" as (b) "[H1 R]"; iExists b; iFrame "H1".
      iModIntro; iSplit.
      + iIntros "H1"; iApply "Hclose".
        iExists b; iFrame.
      + iIntros (_) "[[% H1] _]"; subst.
        iDestruct "Hclose" as "[_ Hclose]"; iApply ("Hclose" $! tt).
        rewrite bi.sep_emp; iFrame "R"; iExists true; iFrame.
    - iPureIntro. iIntros (rho') "[% [_ H]]".
      unfold PROPx, LOCALx, SEPx; simpl; auto.
  Qed.

  Program Definition acquire_spec_inv_atomic :=
    ATOMIC TYPE (ProdType (ConstType val) Mpred) INVS empty
    WITH p, R
    PRE [ tptr t_lock ]
       PROP ()
       PARAMS (p)
       SEP () | (inv_for_lock p R)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (R) | (inv_for_lock p R).

  Lemma acquire_inv: funspec_sub (snd acquire_spec) acquire_spec_inv_atomic.
  Proof.
    split; first done. intros. simpl in *. destruct x2 as ((p, R), Q). Intros.
    unfold rev_curry, tcurry; simpl. iIntros "H !>".
    iExists (p, Q ∗ R), emp; simpl.
    rewrite bi.emp_sep. iSplit.
    - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; monPred.unseal.
      iDestruct "H" as "(% & % & _ & H & _)".
      do 4 (iSplit; auto).
      unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
      iMod "H" as (_) "[H Hclose]".
      unfold inv_for_lock at 1.
      iDestruct "H" as (b) "[H1 R]"; iExists b; iFrame "H1".
      iModIntro; iSplit.
      + iIntros "H1"; iApply "Hclose".
        iExists b; iFrame.
      + iIntros (_) "[[% H1] _]"; subst.
        iFrame "R".
        iDestruct "Hclose" as "[_ Hclose]"; iApply ("Hclose" $! tt).
        rewrite bi.sep_emp; iExists true; iFrame.
    - iPureIntro. iIntros (rho') "[% [_ H]]".
      unfold PROPx, LOCALx, SEPx; simpl. rewrite bi.sep_assoc //.
  Qed.

(*  (* "lock variant" version where the lock has a parameter held in the global state *)
  Program Definition acquire_spec_inv_variant :=
    ATOMIC TYPE (ProdType (ConstType _) (ArrowType (DependentType 0) Mpred)) OBJ x INVS empty
    WITH p, R
    PRE [ tptr t_lock ]
       PROP ()
       PARAMS (p)
       SEP () | (inv_for_lock p (R x))
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP () | (inv_for_lock p (R x) * R x).
  Next Obligation.
  Proof.
    intros; rewrite !approx_sepcon; do 2 f_equal; auto.
    rewrite approx_idem; auto.
  Qed.

  Lemma acquire_inv_variant: funspec_sub (snd acquire_spec) acquire_spec_inv_variant.
  Proof.
    apply prove_funspec_sub.
    split; auto. intros. simpl in *. destruct x2 as ((p, R), Q). Intros.
    unfold rev_curry, tcurry; simpl. iIntros "H !>". iExists nil.
    iExists (p, Q), emp; simpl.
    rewrite bi.emp_sep. iSplit.
    - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl.
      iDestruct "H" as "(% & % & _ & H & _)".
      do 4 (iSplit; auto).
      unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
      iMod "H" as (x) "[H Hclose]".
      unfold inv_for_lock at 1.
      iDestruct "H" as (b) "[H1 R]"; iExists b; iFrame "H1".
      iModIntro; iSplit.
      + iIntros "H1"; iApply "Hclose".
        iExists b; iFrame.
      + iIntros (_) "[[% H1] _]"; subst.
        iDestruct "Hclose" as "[_ Hclose]"; iApply ("Hclose" $! tt).
        rewrite bi.sep_emp; iFrame "R"; iExists true; iFrame.
    - iPureIntro. iIntros (rho') "[% [_ H]]".
      unfold PROPx, LOCALx, SEPx; simpl; auto.
  Qed.*)

  Program Definition release_spec_inv_atomic :=
    ATOMIC TYPE (ProdType (ConstType val) Mpred) INVS empty
    WITH p, R
    PRE [ tptr t_lock ]
       PROP ()
       PARAMS (p)
       SEP (<affine> (R ∗ R -∗ False)) | (R ∗ inv_for_lock p R)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP () | (inv_for_lock p R).

  Lemma release_inv: funspec_sub (snd release_spec) release_spec_inv_atomic.
  Proof.
    split; first done. intros ((p, R), Q) ?. simpl in *. Intros.
    unfold rev_curry, tcurry; simpl. iIntros "H !>".
    iExists (p, Q), emp; simpl.
    rewrite bi.emp_sep. iSplit.
    - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; monPred.unseal.
      iDestruct "H" as "(% & % & _ & H & excl & _)".
      do 4 (iSplit; auto).
      unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
      iMod "H" as (_) "[[R H] Hclose]".
      unfold inv_for_lock at 1.
      iDestruct "H" as (b) "[H1 R1]"; destruct b.
      + iExists tt; iFrame "H1".
        iModIntro; iSplit.
        * iIntros "H1"; iFrame "excl"; iApply "Hclose".
          iFrame "R"; iExists true; iFrame.
        * iIntros (_) "[H1 _]".
          iDestruct "excl" as "_".
          iDestruct "Hclose" as "[_ Hclose]"; iApply ("Hclose" $! tt).
          rewrite bi.sep_emp; iExists false; iFrame.
      + iAssert (▷ False) with "[excl R R1]" as ">[]".
        rewrite bi.affinely_elim; iApply "excl"; by iFrame.
    - iPureIntro. iIntros (rho') "[% [_ H]]".
      unfold PROPx, LOCALx, SEPx; simpl; auto.
  Qed.

  Program Definition release_spec_inv_atomic1 :=
    ATOMIC TYPE (ConstType val) OBJ R INVS empty
    WITH p
    PRE [ tptr t_lock ]
       PROP ()
       PARAMS (p)
       SEP () | (<affine> (R ∗ R -∗ False) ∗ R ∗ inv_for_lock p R)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP () | (inv_for_lock p R).

  Lemma release_inv_atomic: funspec_sub (snd release_spec) release_spec_inv_atomic1.
  Proof.
    split; first done. intros (p, Q) ?. simpl in *. Intros.
    unfold rev_curry, tcurry; simpl. iIntros "H !>".
    iExists (p, Q), emp; simpl.
    rewrite bi.emp_sep. iSplit.
    - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; monPred.unseal.
      iDestruct "H" as "(% & % & _ & H & _)".
      do 4 (iSplit; auto).
      unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
      iMod "H" as (R) "[H Hclose]".
      unfold inv_for_lock at 1.
      iDestruct "H" as "(excl & R & H1)"; iExists tt.
      iDestruct "H1" as (b) "[H1 R1]".
      destruct b.
      iFrame "H1".
      iModIntro; iSplit.
      + iIntros "H1"; iApply "Hclose".
        iFrame "excl R"; iExists true; iFrame.
      + iIntros (_) "[H1 _]".
        iDestruct "Hclose" as "[_ Hclose]"; iApply ("Hclose" $! tt).
        rewrite bi.sep_emp; iExists false; iFrame.
      + iAssert (▷ False) with "[excl R R1]" as ">[]".
        rewrite bi.affinely_elim; iApply "excl"; by iFrame.
    - iPureIntro. iIntros (rho') "[% [_ H]]".
      unfold PROPx, LOCALx, SEPx; simpl; auto.
  Qed.

(*  Program Definition release_spec_inv_variant :=
    ATOMIC TYPE (ProdType (ProdType (ConstType _) (ArrowType (DependentType 0) Mpred)) (DependentType 0)) OBJ y INVS empty
    WITH p, R, x
    PRE [ tptr t_lock ]
       PROP ()
       PARAMS (p)
       SEP (<affine> (R ∗ R -∗ False)) | (R x ∗ inv_for_lock p (R y))
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP () | (inv_for_lock p (R x)).
  Next Obligation.
  Proof.
    rewrite !approx_andp; f_equal.
    apply exclusive_mpred'_super_non_expansive.
  Qed.
  Next Obligation.
  Proof.
    intros; rewrite !approx_sepcon approx_idem; f_equal.
    apply inv_for_lock_super_non_expansive.
  Qed.
  Next Obligation.
  Proof.
    intros; rewrite !approx_sepcon; f_equal.
    apply inv_for_lock_super_non_expansive.
  Qed.

  Lemma release_inv_variant: funspec_sub (snd release_spec) release_spec_inv_variant.
  Proof.
    apply prove_funspec_sub.
    split; auto. intros. simpl in *. destruct x2 as (((p, R), x), Q). Intros.
    unfold rev_curry, tcurry; simpl. iIntros "H !>". iExists nil.
    iExists (p, Q), emp; simpl.
    rewrite bi.emp_sep. iSplit.
    - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl.
      iDestruct "H" as "(% & % & _ & H & excl & _)".
      do 4 (iSplit; auto).
      unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
      iMod "H" as (y) "[[R H] Hclose]".
      unfold inv_for_lock at 1.
      iDestruct "H" as (b) "[H1 R1]"; destruct b.
      + iExists tt; iFrame "H1".
        iModIntro; iSplit.
        * iIntros "H1"; iFrame "excl"; iApply "Hclose".
          iFrame "R"; iExists true; iFrame.
        * iIntros (_) "[H1 _]".
          iDestruct "excl" as "_".
          iDestruct "Hclose" as "[_ Hclose]"; iApply ("Hclose" $! tt).
          rewrite bi.sep_emp; iExists false; iFrame.
      + iAssert (▷ FF) with "[excl R R1]" as ">[]".
        iNext. iApply weak_exclusive'_conflict; iFrame; iFrame.
    - iPureIntro. iIntros (rho') "[% [_ H]]".
      unfold PROPx, LOCALx, SEPx; simpl; auto.
  Qed.*)

  Program Definition acquire_spec_inv :=
    TYPE (ProdType (ConstType (Qp * lock_handle)) Mpred)
    WITH sh : _, h : _, R : _
    PRE [ tptr t_lock ]
       PROP ()
       PARAMS (ptr_of h)
       SEP (lock_inv sh h R)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (lock_inv sh h R; ▷ R).

  Lemma acquire_inv_simple: funspec_sub (snd acquire_spec) acquire_spec_inv.
  Proof.
    split; first done. intros ((sh, h), R) ?. simpl in *. Intros.
    unfold rev_curry, tcurry. iIntros "H !>".
    iExists (ptr_of(lock_impl := atomic_impl) h, lock_inv(lock_impl := atomic_impl) sh h R ∗ ▷ R), emp; simpl.
    rewrite bi.emp_sep. iSplit.
    - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx; simpl; monPred.unseal.
      iDestruct "H" as "(_ & % & _ & H & _)".
      do 4 (iSplit; auto).
      unfold lock_inv; simpl; destruct h as ((v, i), g).
      iDestruct "H" as "(([% %] & #H) & H2)".
      unfold atomic_shift. iAuIntro. unfold atomic_acc; simpl.
      iInv "H" as "inv" "Hclose".
      iDestruct "inv" as "[inv | >inv]".
      iDestruct "inv" as (b) "[>H1 R]".
      iApply fupd_mask_intro; try set_solver. iIntros "Hclose'".
      iExists b; iFrame "H1"; iSplit.
      + iIntros "H1"; iFrame "H2".
        iMod "Hclose'"; iApply "Hclose".
        iLeft; iExists b; iFrame.
      + iIntros (_) "[[% H1] _]"; subst.
        rewrite -> prop_true_andp by auto.
        iFrame "H H2 R".
        iMod "Hclose'"; iApply "Hclose".
        iLeft; iExists true; iFrame; auto.
      + iDestruct (own_valid_2 with "[$H2 $inv]") as %(? & J & ?).
        apply sepalg.join_comm, join_Tsh in J as []; contradiction.
    - iPureIntro. iIntros (rho') "[% [_ H]]".
      unfold PROPx, LOCALx, SEPx; simpl. rewrite <- sepcon_assoc; auto.
  Qed.

  Program Definition release_spec_inv :=
    TYPE (ProdType (ProdType (ProdType (ConstType _) Mpred) Mpred) Mpred)
    WITH sh : _, h : _, R : _, P : _, Q : _
    PRE [ tptr t_lock ]
       PROP ()
       PARAMS (ptr_of h)
       SEP (<affine> (R ∗ R -∗ False); lock_inv sh h R; P; lock_inv sh h R * P -* Q * R)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (▷ Q).
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as ((((?, ?), ?), ?), ?); simpl.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; do 3 f_equal;
      rewrite -> !bi.sep_emp, ?approx_sepcon, ?approx_idem.
    f_equal.
    { rewrite !approx_andp; f_equal.
      apply exclusive_mpred_super_non_expansive. }
    f_equal.
    { apply lock_inv_super_non_expansive. }
    f_equal.
    setoid_rewrite wand_nonexpansive; rewrite !approx_sepcon; do 2 f_equal; rewrite !approx_idem; f_equal.
    apply lock_inv_super_non_expansive.
  Qed.
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as ((((?, ?), ?), ?), ?); simpl.
    unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 f_equal;
      rewrite -> !bi.sep_emp, ?approx_sepcon, ?approx_idem.
    setoid_rewrite later_nonexpansive; rewrite approx_idem; auto.
  Qed.

  Lemma release_inv_simple: funspec_sub (snd release_spec) release_spec_inv.
  Proof.
    apply prove_funspec_sub.
    split; auto. intros. simpl in *. destruct x2 as ((((sh, h), R), P), Q). Intros.
    unfold rev_curry, tcurry. iIntros "H !>". iExists nil.
    iExists (@ptr_of atomic_impl h, ▷ Q), emp. simpl in *.
    rewrite bi.emp_sep. iSplit.
    - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl.
      iDestruct "H" as "(_ & % & _ & H)".
      do 4 (iSplit; auto).
      iDestruct "H" as "(H5 & H2 & H3 & H4 & _)".
      unfold lock_inv; simpl; unfold atomic_lock_inv; destruct h as ((v, i), g).
      iDestruct "H2" as "(([% %] & #H) & H2)".
      rewrite -> prop_true_andp by auto.
      unfold atomic_shift. iAuIntro. unfold atomic_acc; simpl.
      iInv "H" as "inv" "Hclose".
      iDestruct "inv" as "[inv | >inv]".
      unfold inv_for_lock at 3.
      iDestruct "inv" as (b) "[>H1 R]".
      iExists tt.
      destruct b.
      + iApply fupd_mask_intro; try set_solver. iIntros "Hclose'".
        iFrame "H1"; iSplit.
        * iIntros "H1". iFrame. iMod "Hclose'"; iApply "Hclose".
          iLeft; unfold inv_for_lock; iExists true; iFrame; auto.
        * iIntros (_) "[H1 _]". iDestruct "H5" as "_". iPoseProof ("H4" with "[$H2 $H3]") as "[$ HR]"; auto.
          iMod "Hclose'"; iMod ("Hclose" with "[-]"); last done.
          iLeft; unfold inv_for_lock; iExists false; iFrame; auto.
      + iPoseProof ("H4" with "[$H2 $H3]") as "[$ HR]"; auto.
        iAssert (▷FF) with "[H5 R HR]" as ">[]".
        iNext; iApply weak_exclusive_conflict; iFrame; iFrame.
      + iDestruct (own_valid_2 with "[$H2 $inv]") as %(? & J & ?).
        apply sepalg.join_comm, join_Tsh in J as []; contradiction.
    - iPureIntro. iIntros (rho') "[% [_ H]]".
      unfold PROPx, LOCALx, SEPx; simpl; auto.
  Qed.

  Lemma release_simple : funspec_sub (snd release_spec) release_spec_simple.
  Proof.
    apply prove_funspec_sub.
    split; auto. intros. simpl in *. destruct x2 as ((sh, h), R). Intros.
    unfold rev_curry, tcurry. iIntros "H !>". iExists nil.
    iExists (@ptr_of atomic_impl h, @lock_inv atomic_impl sh h R), emp. simpl in *.
    rewrite bi.emp_sep. iSplit.
    - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl.
      iDestruct "H" as "([% _] & % & _ & H)".
      do 4 (iSplit; auto).
      iDestruct "H" as "(H5 & H2 & H3 & _)".
      unfold lock_inv; simpl; unfold atomic_lock_inv; destruct h as ((v, i), g).
      iDestruct "H2" as "(([_ %] & #H) & H2)".
      rewrite -> prop_true_andp by auto.
      unfold atomic_shift. iAuIntro. unfold atomic_acc; simpl.
      iInv "H" as "inv" "Hclose".
      iDestruct "inv" as "[inv | >inv]".
      unfold inv_for_lock at 3.
      iDestruct "inv" as (b) "[>H1 R]".
      iExists tt.
      destruct b.
      + iApply fupd_mask_intro; try set_solver. iIntros "Hclose'".
        iFrame "H1"; iSplit.
        * iIntros "H1". iFrame. iMod "Hclose'"; iApply "Hclose".
          iLeft; unfold inv_for_lock; iExists true; iFrame; auto.
        * iIntros (_) "[H1 _]". iDestruct "H5" as "_". iDestruct "R" as ">_". iFrame "H H2".
          iMod "Hclose'"; iApply "Hclose".
          iLeft; unfold inv_for_lock; iExists false; iFrame; auto.
      + iAssert (▷FF) with "[H5 R H3]" as ">[]".
        iNext; iApply weak_exclusive_conflict; iFrame; iFrame.
      + iDestruct (own_valid_2 with "[$H2 $inv]") as %(? & J & ?).
        apply sepalg.join_comm, join_Tsh in J as []; contradiction.
    - iPureIntro. iIntros (rho') "[% [_ H]]".
      unfold PROPx, LOCALx, SEPx; simpl; auto.
  Qed.

  Program Definition release_spec_self :=
    TYPE (ProdType (ConstType _) Mpred)
    WITH sh : _, h : _, R : _
    PRE [ tptr t_lock ]
       PROP ()
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
      rewrite -> !bi.sep_emp, ?approx_sepcon, ?approx_idem.
    f_equal.
    setoid_rewrite (@lock_inv_super_non_expansive atomic_impl); do 2 f_equal.
    rewrite !approx_sepcon approx_idem; auto.
  Qed.
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as ((?, ?), ?); simpl.
    reflexivity.
  Qed.

  Lemma release_self : funspec_sub (snd release_spec) release_spec_self.
  Proof.
    apply prove_funspec_sub.
    split; auto. intros. simpl in *. destruct x2 as ((sh, h), R). Intros.
    unfold rev_curry, tcurry. iIntros "H !>". iExists nil.
    destruct h as ((v, N), g).
    iExists (v, emp), emp. simpl in *.
    rewrite bi.emp_sep. iSplit.
    - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl.
      iDestruct "H" as "(_ & % & _ & H)".
      do 4 (iSplit; auto).
      iDestruct "H" as "(H & R & _)".
      unfold lock_inv; simpl.
      iDestruct "H" as "(([% %] & #H) & H2)".
      unfold atomic_shift. iAuIntro. unfold atomic_acc; simpl.
      iInv "H" as "inv" "Hclose".
      iDestruct "inv" as "[inv | >inv]".
      unfold inv_for_lock at 2.
      iDestruct "inv" as (b) "[>H1 HR]".
      iExists tt.
      destruct b.
      + iApply fupd_mask_intro; try set_solver. iIntros "Hclose'".
        iFrame "H1"; iSplit.
        * iIntros "H1". iFrame. iMod "Hclose'"; iApply "Hclose".
          iLeft; unfold inv_for_lock; iExists true; iFrame; auto.
        * iIntros (_) "[H1 _]".
          iMod "Hclose'"; iApply "Hclose".
          iLeft; unfold inv_for_lock; iExists false; iFrame; auto.
      + iDestruct "HR" as "[>Hg ?]".
        iDestruct (own_valid_2 with "[$H2 $Hg]") as %(? & J & ?).
        apply sepalg.join_self, identity_share_bot in J; contradiction.
      + iDestruct (own_valid_2 with "[$H2 $inv]") as %(? & J & ?).
        apply sepalg.join_comm, join_Tsh in J as []; contradiction.
    - iPureIntro. iIntros (rho') "[% [_ H]]".
      unfold PROPx, LOCALx, SEPx; simpl; auto.
  Qed.

  Lemma freelock_inv: funspec_sub (snd freelock_spec) lock_specs.freelock_spec.
  Proof.
    apply prove_funspec_sub.
    split; auto. intros. simpl in *. destruct x2 as ((h, R), P). Intros.
    iIntros "H". iExists nil, (@ptr_of atomic_impl h), P.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl.
    rewrite !bi.sep_emp. iDestruct "H" as "(_ & % & % & H1 & HP & R)".
    unfold lock_inv; simpl; unfold atomic_lock_inv; destruct h as ((v, i), g).
    iDestruct "H1" as "(([% %] & #H) & H2)".
    iInv "H" as "[inv | inv]" "Hclose".
    iDestruct "inv" as (b) "[>a HR]".
    destruct b.
    iMod "HR" as "_"; iDestruct "R" as "_".
    iMod ("Hclose" with "[H2]") as "_".
    { iRight; auto. }
    iFrame "HP"; iModIntro; iSplit.
    - do 3 (iSplit; auto).
      iExists _; iApply "a".
    - iPureIntro; intros; Intros; cancel.
      apply andp_left2; auto.
    - iAssert (▷FF) with "[R HP HR H2]" as ">[]".
      iNext; iApply "R"; iFrame; iSplit; auto.
    - iAssert (▷FF) with "[H2 inv]" as ">[]".
      iNext; iApply cinv_own_excl; [|iFrame]; auto.
  Qed.

  Lemma freelock_simple: funspec_sub (snd freelock_spec) freelock_spec_simple.
  Proof.
    eapply funspec_sub_trans, freelock_simple; apply freelock_inv.
  Qed.

  Program Definition freelock_spec_self :=
    TYPE (ProdType (ConstType _) Mpred)
    WITH sh1 : _, sh2 : _, h : _, R : _
    PRE [ tptr t_lock ]
       PROP (sh2 <> Share.bot; sepalg.join sh1 sh2 Tsh)
       PARAMS (ptr_of h)
       SEP (lock_inv sh1 h (self_part sh2 h * R); self_part sh2 h)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP ().
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as (((?, ?), ?), ?); simpl.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; do 3 f_equal;
      rewrite -> !bi.sep_emp, ?approx_sepcon, ?approx_idem.
    f_equal.
    setoid_rewrite (@lock_inv_super_non_expansive atomic_impl); do 2 f_equal.
    rewrite !approx_sepcon approx_idem; auto.
  Qed.
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as (((?, ?), ?), ?); simpl.
    unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 f_equal;
      rewrite -> !bi.sep_emp, ?approx_sepcon, ?approx_idem.
  Qed.

  Lemma freelock_self : funspec_sub (snd freelock_spec) freelock_spec_self.
  Proof.
    eapply funspec_sub_trans; [apply freelock_inv|].
    apply prove_funspec_sub.
    split; auto; intros ? (((sh1, sh2), h), R) ?; Intros; simpl.
    iIntros "H !>".
    iExists nil, (h, self_part sh2 h * R, emp), emp.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl.
    rewrite !bi.emp_sep !bi.sep_emp.
    iDestruct "H" as "((% & % & _) & % & % & H)".
    iSplit; [do 3 (iSplit; [auto|])|].
    - iAssert (⌜sh1 <> Share.bot⌝) with "[H]" as %?.
      { iDestruct "H" as "[l _]"; iDestruct (lock_inv_share with "l") as %[]; auto. }
      erewrite -> self_part_eq, lock_inv_share_join by eauto; iFrame.
      iSplit; auto; iIntros "H".
      rewrite <- sepcon_assoc, self_part_eq by auto.
      destruct h as ((p, i), g); unfold lock_inv; simpl.
      iDestruct "H" as "[[[_ g1] [_ g2]] _]".
      iApply (cinv_own_excl with "[$g1 $g2]"); auto.
    - iPureIntro; intros; Intros.
      rewrite bi.emp_sep; apply andp_left2; auto.
  Qed.

End PROOFS.

(* when interacting with atomic updates, we need to unfold the definition of lock_inv and split its pieces *)
Ltac unfold_lock_inv := match goal with |-context[lock_inv _ ?h _] =>
  unfold lock_inv; simpl; let v := fresh "v" in let N := fresh "N" in let g := fresh "g" in destruct h as ((v, N), g) end.
