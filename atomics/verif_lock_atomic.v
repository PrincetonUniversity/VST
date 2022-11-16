Require Import VST.veric.rmaps.
Require Import VST.concurrency.conclib.
Require Import VST.concurrency.ghosts.
Require Import VST.concurrency.cancelable_invariants.
Require Export VST.concurrency.lock_specs.
Require Import VST.floyd.library.
Require Export VST.atomics.SC_atomics_base.
Require Export VST.atomics.verif_lock.
Require Export VST.atomics.SC_atomics.
Require Import VST.concurrency.threads.

Section PROOFS.

  #[local] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
  Definition Vprog : varspecs. mk_varspecs prog. Defined.

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
    POST [ tptr t_lock ] EX p,
       PROP ()
       RETURN (p)
       SEP (mem_mgr gv; atomic_int_at Ews (vint 1) p).

  Definition freelock_spec :=
    DECLARE _freelock
    WITH p : val
    PRE [ tptr t_lock ]
     PROP ()
     PARAMS (p)
     SEP (EX v : val, atomic_int_at Ews v p)
   POST[ tvoid ]
     PROP ()
     LOCAL ()
     SEP ().

  Program Definition release_spec :=
    DECLARE _release
    ATOMIC TYPE (rmaps.ConstType val) INVS empty
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
    ATOMIC TYPE (rmaps.ConstType _) OBJ l INVS empty
    WITH p
    PRE [ tptr t_lock ]
       PROP ()
       PARAMS (p)
       SEP () | (atomic_int_at Ews (Val.of_bool l) p)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP () | (!!(l = false) && atomic_int_at Ews (vint 1) p).

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
    assert_PROP (is_pointer_or_null p) by entailer.
    forward_call (p).
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
      iExists Ews. iModIntro. iSplitL "a".
      + iSplit.
        * iPureIntro. apply writable_Ews.
        * iApply atomic_int_at__. iAssumption.
      + iIntros "AA".
        iPoseProof (sepcon_emp (atomic_int_at Ews (vint 0) p)) as "HA".
        iSpecialize ("HA" with "AA"). iMod ("H" $! tt with "HA"). auto.
    - entailer !.
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
        * forward_if; try contradiction. forward. entailer!.
        * forward_if; try discriminate. forward. entailer!.
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

  #[global] Instance atomic_int_timeless sh v p : Timeless (atomic_int_at sh v p).
  Proof.
    apply timeless'_timeless; auto.
  Qed.

  #[global] Instance inv_for_lock_timeless v R {H : Timeless R} : Timeless (inv_for_lock v R).
  Proof.
    unfold inv_for_lock.
    apply bi.exist_timeless; intros []; apply _.
  Qed.

  Lemma release_nonatomic: funspec_sub (snd release_spec) release_spec_nonatomic.
  Proof.
    apply prove_funspec_sub.
    split; auto. intros. simpl in *. Intros.
    unfold rev_curry, tcurry; simpl. iIntros "H !>". iExists nil, (x2, atomic_int_at Ews (vint 0) x2), emp.
    rewrite emp_sepcon. iSplit.
    - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl.
      iDestruct "H" as "(% & % & _ & H & _)".
      do 4 (iSplit; auto).
      unfold atomic_shift; iAuIntro; unfold atomic_acc; simpl.
      iExists tt; iFrame "H".
      iApply fupd_mask_intro; first done; iIntros "Hclose".
      iSplit; [iIntros "$" | iIntros (_) "[$ _]"]; auto.
    - iPureIntro. intros. Intros. rewrite emp_sepcon. auto.
  Qed.



  (* Asymmetric consequence means we can't prove the specs from lock_specs directly,
     but we can wrap a view shift around them. Paradoxically, as shown in verif_lock,
     we would be able to prove lock_specs directly (without using funspec_sub), but
     that conflicts with the "one spec in Gprog" approach. *)

  #[local] Obligation Tactic := intros.

  #[export] Program Instance atomic_impl : lock_impl := { t_lock := Tstruct _atom_int noattr; lock_handle := val * namespace * ghosts.gname;
    ptr_of h := let '(v, _, _) := h in v; lock_inv sh h R := let '(v, N, g) := h in !!(sh <> Share.bot /\ isptr v) && cinv N g (inv_for_lock v R) * cinv_own g sh }.
  Next Obligation.
  Proof.
    destruct h as ((?, ?), ?).
    apply sepcon_nonexpansive, const_nonexpansive.
    apply @conj_nonexpansive; [apply const_nonexpansive|].
    apply cinv_nonexpansive2, inv_for_lock_nonexpansive.
  Qed.
  Next Obligation.
  Proof.
    destruct h as ((?, ?), ?); simpl.
    destruct (isptr_dec v).
    rewrite !prop_true_andp; auto.
    rewrite <- !sepcon_assoc, (sepcon_comm (_ * cinv_own _ _)), !sepcon_assoc.
    unfold cinv_own at 1 2; erewrite <- own_op by eauto.
    rewrite <- sepcon_assoc; f_equal.
    rewrite {3}(bi.persistent_sep_dup (cinv n g _)); auto.
    { split; auto; intros ?; subst. apply join_Bot in H1 as []; contradiction. }
    { rewrite -> prop_false_andp, !FF_sepcon, prop_false_andp, FF_sepcon; auto; intros []; contradiction. }
  Qed.
  Next Obligation.
  Proof.
    unfold exclusive_mpred; destruct h as ((?, ?), ?); Intros.
    unfold cinv_own; sep_apply own_op'.
    Intros ?; Intros.
    apply sepalg.join_self, identity_share_bot in H0; contradiction.
  Qed.
  Next Obligation.
  Proof.
    destruct h as ((?, ?), ?); simpl; entailer!.
  Qed.

  Definition name_of (h : lock_handle) := let '(_, N, _) := h in N.
  Definition ghost_of (h : lock_handle) := let '(_, _, g) := h in g.
  #[global] Instance lock_handle_inhabited : Inhabitant lock_handle := (Vundef, nroot, O).

  (* Since a lock's namespace is known, the ghost name is the only part that needs to be existentially quantified. *)
  Definition self_part sh h := cinv_own (ghost_of h) sh.

  Lemma self_part_exclusive : forall sh h, sh <> Share.bot -> exclusive_mpred (self_part sh h).
  Proof.
    intros; unfold exclusive_mpred, self_part.
    unfold cinv_own; rewrite own_op'; Intros ?.
    apply sepalg.join_self, identity_share_bot in H0; contradiction.
  Qed.

  Lemma self_part_eq : forall sh1 sh2 h R, sh2 <> Share.bot -> lock_inv sh1 h (self_part sh2 h * R) * self_part sh2 h =
    lock_inv sh1 h (self_part sh2 h * R) * lock_inv sh2 h (self_part sh2 h * R).
  Proof.
    intros; unfold lock_inv; destruct h as ((v, N), g); simpl.
    destruct (eq_dec sh1 Share.bot).
    { rewrite -> prop_false_andp, !FF_sepcon; auto; intros []; contradiction. }
    destruct (isptr_dec v).
    rewrite -> !prop_true_andp by auto.
    unfold self_part at 2; rewrite {1}(bi.persistent_sep_dup (cinv N g _)).
    rewrite <- !sepcon_assoc; f_equal.
    rewrite -> (sepcon_comm (_ * _) (cinv _ _ _)), <- sepcon_assoc; reflexivity.
    { rewrite -> prop_false_andp, !FF_sepcon; auto; intros []; contradiction. }
  Qed.

  (* caller can request the lock's namespace *)
  Program Definition makelock_spec_inv :=
    TYPE (ProdType (ConstType (globals * namespace)) (ArrowType (ConstType lock_handle) Mpred)) WITH gv: _, N : _, R : _
    PRE [ ]
       PROP ()
       PARAMS () GLOBALS (gv)
       SEP (mem_mgr gv)
    POST [ tptr t_lock ] (* asymmetric consequence makes this messy *) EX v,
       PROP ()
       RETURN (v)
       SEP (mem_mgr gv; |={⊤}=> EX h, !!(ptr_of h = v /\ name_of h = N) && lock_inv Tsh h (R h)).
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as ((?, ?), ?); simpl.
    reflexivity.
  Qed.
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as ((?, ?), ?); simpl.
    rewrite -> 2approx_exp; apply f_equal; extensionality.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite -> !approx_andp; do 2 apply f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    apply f_equal. setoid_rewrite fupd_nonexpansive; do 2 apply f_equal.
    rewrite !approx_exp; apply f_equal; extensionality.
    rewrite !approx_andp; f_equal.
    apply lock_inv_super_non_expansive.
  Qed.

  (* These lemmas can be used to attach an invariant to an existing lock. *)
  Lemma make_lock_inv_1 : forall v N (R : lock_handle -> mpred), atomic_int_at Ews (vint 1) v |-- (*|={⊤}=>*) @fupd mpred (bi_fupd_fupd(BiFUpd := mpred_bi_fupd)) ⊤ ⊤ (EX h, !!(ptr_of h = v /\ name_of h = N) && lock_inv Tsh h (R h)).
  Proof.
    intros.
    iIntros "a".
    iDestruct (atomic_int_isptr with "a") as %Ha.
    iMod (cinv_alloc_dep with "[a]") as (g) "[Hi Hg]";
      [| iExists (v, N, g); unfold lock_inv; simpl; iFrame "Hi Hg"; auto].
    iIntros (?) "!>"; unfold inv_for_lock.
    iExists true; iFrame.
  Qed.

  Lemma make_lock_inv_0_self : forall v N R sh1 sh2, sh1 <> Share.bot -> sepalg.join sh1 sh2 Tsh ->
    (atomic_int_at Ews (vint 0) v * R) |-- @fupd mpred (bi_fupd_fupd(BiFUpd := mpred_bi_fupd)) ⊤ ⊤ (EX h, !!(ptr_of h = v /\ name_of h = N) && lock_inv sh1 h (R * self_part sh2 h)).
  Proof.
    intros.
    iIntros "[a R]".
    iDestruct (atomic_int_isptr with "a") as %Ha.
    iMod (own_alloc(RA := share_ghost) with "[$]") as (g) "g"; first done.
    setoid_rewrite (own_op(RA := share_ghost) _ _ _ _ _ H0); iDestruct "g" as "[g1 g2]".
    iMod (inv_alloc with "[a R g2]") as "I";
      [| iExists (v, N, g); unfold lock_inv; simpl; iFrame; auto].
    iIntros "!>"; unfold inv_for_lock.
    iLeft; iExists false; iFrame; auto.
  Qed.

  Lemma make_lock_inv_0' : forall v N (R : lock_handle -> mpred), (atomic_int_at Ews (vint 0) v * ALL g, R g) |-- @fupd mpred (bi_fupd_fupd(BiFUpd := mpred_bi_fupd)) ⊤ ⊤ (EX h, !!(ptr_of h = v /\ name_of h = N) && lock_inv Tsh h (R h)).
  Proof.
    intros.
    iIntros "[a R]".
    iDestruct (atomic_int_isptr with "a") as %Ha.
    iMod (cinv_alloc_dep with "[a R]") as (g) "[Hi Hg]";
      [| iExists (v, N, g); unfold lock_inv; simpl; iFrame "Hi Hg"; auto].
    iIntros (?) "!>"; unfold inv_for_lock.
    iExists false; iFrame; auto.
  Qed.

  Lemma make_lock_inv_0 : forall v N R, atomic_int_at Ews (vint 0) v * R |-- @fupd mpred (bi_fupd_fupd(BiFUpd := mpred_bi_fupd)) ⊤ ⊤ (EX h, !!(ptr_of h = v /\ name_of h = N) && lock_inv Tsh h R).
  Proof.
    intros.
    eapply derives_trans, make_lock_inv_0'.
    cancel.
    apply allp_right; intros; auto.
  Qed.

  Lemma makelock_inv: funspec_sub (snd makelock_spec) makelock_spec_inv.
  Proof.
    apply prove_funspec_sub.
    split; auto. intros. simpl in *. destruct x2 as [[gv N] R]. Intros.
    iIntros "H !>". iExists nil, gv, emp. rewrite emp_sepcon. iSplit; auto.
    iPureIntro. intros. Intros. rewrite emp_sepcon. Intros x; Exists x.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx; simpl. Intros.
    apply andp_right; [apply andp_left1, derives_refl | apply andp_left2].
    cancel.
    apply make_lock_inv_1.
  Qed.

  #[local] Obligation Tactic := atomic_nonexpansive_tac.

  Lemma inv_for_lock_super_non_expansive : forall p R n,
    compcert_rmaps.RML.R.approx n (inv_for_lock p R) =
    compcert_rmaps.RML.R.approx n (inv_for_lock p (compcert_rmaps.RML.R.approx n R)).
  Proof.
    intros; apply nonexpansive_super_non_expansive, inv_for_lock_nonexpansive.
  Qed.
  #[local] Hint Resolve inv_for_lock_super_non_expansive : core.

  (* Yet another variant: we only learn the lock invariant after a successful acquire. *)
  Program Definition acquire_spec_inv_atomic1 :=
    ATOMIC TYPE (ConstType _) OBJ R INVS empty
    WITH p
    PRE [ tptr t_lock ]
       PROP ()
       PARAMS (p)
       SEP () | (inv_for_lock p R)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP () | (inv_for_lock p R * R).

  Lemma acquire_inv_atomic: funspec_sub (snd acquire_spec) acquire_spec_inv_atomic1.
  Proof.
    apply prove_funspec_sub.
    split; auto. intros. simpl in *. destruct x2 as (p, Q). Intros.
    unfold rev_curry, tcurry; simpl. iIntros "H !>". iExists nil.
    iExists (p, Q), emp; simpl.
    rewrite emp_sepcon. iSplit.
    - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl.
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
        rewrite sepcon_emp; iFrame "R"; iExists true; iFrame.
    - iPureIntro. iIntros (rho') "[% [_ H]]".
      unfold PROPx, LOCALx, SEPx; simpl; auto.
  Qed.

  Program Definition acquire_spec_inv_atomic :=
    ATOMIC TYPE (ProdType (ConstType _) Mpred) INVS empty
    WITH p, R
    PRE [ tptr t_lock ]
       PROP ()
       PARAMS (p)
       SEP () | (inv_for_lock p R)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (R) | (inv_for_lock p R).
  Next Obligation.
  Proof.
    intros; rewrite !approx_sepcon; f_equal; auto.
  Qed.
  Next Obligation.
  Proof.
    rewrite approx_idem; auto.
  Qed.

  Lemma acquire_inv: funspec_sub (snd acquire_spec) acquire_spec_inv_atomic.
  Proof.
    apply prove_funspec_sub.
    split; auto. intros. simpl in *. destruct x2 as ((p, R), Q). Intros.
    unfold rev_curry, tcurry; simpl. iIntros "H !>". iExists nil.
    iExists (p, Q * R), emp; simpl.
    rewrite emp_sepcon. iSplit.
    - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl.
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
        rewrite sepcon_emp; iExists true; iFrame.
    - iPureIntro. iIntros (rho') "[% [_ H]]".
      unfold PROPx, LOCALx, SEPx; simpl. rewrite <- sepcon_assoc; auto.
  Qed.

  (* "lock variant" version where the lock has a parameter held in the global state *)
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
    rewrite emp_sepcon. iSplit.
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
        rewrite sepcon_emp; iFrame "R"; iExists true; iFrame.
    - iPureIntro. iIntros (rho') "[% [_ H]]".
      unfold PROPx, LOCALx, SEPx; simpl; auto.
  Qed.

  Program Definition release_spec_inv_atomic :=
    ATOMIC TYPE (ProdType (ConstType _) Mpred) INVS empty
    WITH p, R
    PRE [ tptr t_lock ]
       PROP ()
       PARAMS (p)
       SEP (weak_exclusive_mpred R && emp) | (R * inv_for_lock p R)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP () | (inv_for_lock p R).
  Next Obligation.
  Proof.
    rewrite !approx_andp; f_equal.
    apply nonexpansive_super_non_expansive, exclusive_mpred_nonexpansive.
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

  Lemma release_inv: funspec_sub (snd release_spec) release_spec_inv_atomic.
  Proof.
    apply prove_funspec_sub.
    split; auto. intros. simpl in *. destruct x2 as ((p, R), Q). Intros.
    unfold rev_curry, tcurry; simpl. iIntros "H !>". iExists nil.
    iExists (p, Q), emp; simpl.
    rewrite emp_sepcon. iSplit.
    - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl.
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
          rewrite sepcon_emp; iExists false; iFrame.
      + iAssert (|> FF) with "[excl R R1]" as ">[]".
        iNext. iApply weak_exclusive_conflict; iFrame; iFrame.
    - iPureIntro. iIntros (rho') "[% [_ H]]".
      unfold PROPx, LOCALx, SEPx; simpl; auto.
  Qed.

  Definition exclusive_mpred' {A} (P : A -> mpred) := forall x y, P x * P y |-- FF.

  Definition weak_exclusive_mpred' {A} (P : A -> mpred) := unfash (fash (ALL x y, P x * P y --> FF)).

  Lemma approx_unfash_fash : forall n P, compcert_rmaps.RML.R.approx n (unfash (fash P)) = unfash (fash (compcert_rmaps.RML.R.approx n P)).
  Proof.
    intros; change unfash with subtypes.unfash; change fash with subtypes.fash; apply predicates_hered.pred_ext; intros ??.
    - destruct H; intros ??; split; [lia | apply H0; auto].
    - destruct (H a); auto; split; auto.
      intros ??; apply H; auto.
  Qed.

  Lemma exclusive_mpred'_super_non_expansive:
    forall {A} (R : A -> mpred) n, compcert_rmaps.RML.R.approx n (weak_exclusive_mpred' R) =
      compcert_rmaps.RML.R.approx n (weak_exclusive_mpred' (fun a => compcert_rmaps.RML.R.approx n (R a))).
  Proof.
    intros; unfold weak_exclusive_mpred'.
    rewrite !approx_unfash_fash; do 2 f_equal.
    setoid_rewrite allp_nonexpansive; do 2 f_equal; extensionality.
    setoid_rewrite allp_nonexpansive; do 2 f_equal; extensionality.
    rewrite approx_imp; do 2 f_equal.
    - apply approx_sepcon.
    - apply approx_FF.
  Qed.

  Lemma fash_allp : forall {B} (F : B -> mpred), fash (allp F) = ALL x, fash (F x).
  Proof.
    intros; apply (subtypes.fash_allp B F).
  Qed.

  Lemma exclusive_weak_exclusive1' : forall {A} (R : A -> mpred) P,
    exclusive_mpred' R ->
    P |-- weak_exclusive_mpred' R.
  Proof.
    intros; unfold weak_exclusive_mpred'; unfold exclusive_mpred' in H.
    rewrite fash_allp unfash_allp; apply allp_right; intros x.
    rewrite fash_allp unfash_allp; apply allp_right; intros y.
    specialize (H x y).
    unseal_derives; apply derives_unfash_fash; auto.
  Qed.

  Lemma exclusive_weak_exclusive' : forall {A} (R : A -> mpred),
    exclusive_mpred' R ->
    seplog.emp |-- weak_exclusive_mpred' R && emp.
  Proof.
    intros; apply andp_right, derives_refl; apply exclusive_weak_exclusive1'; auto.
  Qed.

  Lemma corable_weak_exclusive' : forall {A} (R : A -> mpred), corable (weak_exclusive_mpred' R).
  Proof.
    intros; apply assert_lemmas.corable_unfash, _.
  Qed.

  Lemma weak_exclusive'_conflict : forall {A} P (x y : A),
    (weak_exclusive_mpred' P && emp) * P x * P y |-- FF.
  Proof.
    intros.
    rewrite sepcon_assoc -andp_left_corable; last by (apply corable_weak_exclusive').
    unseal_derives; intros ? [].
    unfold weak_exclusive_mpred in H; specialize (H a ltac:(lia) x y _ _ (ageable.necR_refl _) (predicates_hered.ext_refl _)).
    apply H; auto.
  Qed.

  Program Definition release_spec_inv_variant :=
    ATOMIC TYPE (ProdType (ProdType (ConstType _) (ArrowType (DependentType 0) Mpred)) (DependentType 0)) OBJ y INVS empty
    WITH p, R, x
    PRE [ tptr t_lock ]
       PROP ()
       PARAMS (p)
       SEP (weak_exclusive_mpred' R && emp) | (R x * inv_for_lock p (R y))
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
    rewrite emp_sepcon. iSplit.
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
          rewrite sepcon_emp; iExists false; iFrame.
      + iAssert (|> FF) with "[excl R R1]" as ">[]".
        iNext. iApply weak_exclusive'_conflict; iFrame; iFrame.
    - iPureIntro. iIntros (rho') "[% [_ H]]".
      unfold PROPx, LOCALx, SEPx; simpl; auto.
  Qed.

  #[local] Obligation Tactic := intros.

  Program Definition acquire_spec_inv :=
    TYPE (ProdType (ConstType _) Mpred)
    WITH sh : _, h : _, R : _
    PRE [ tptr t_lock ]
       PROP ()
       PARAMS (ptr_of h)
       SEP (lock_inv sh h R)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (lock_inv sh h R; |> R).
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
    setoid_rewrite later_nonexpansive; rewrite approx_idem; auto.
  Qed.

  Lemma acquire_inv_simple: funspec_sub (snd acquire_spec) acquire_spec_inv.
  Proof.
    apply prove_funspec_sub.
    split; auto. intros. simpl in *. destruct x2 as ((sh, h), R). Intros.
    unfold rev_curry, tcurry. iIntros "H !>". iExists nil.
    iExists (@ptr_of atomic_impl h, @lock_inv atomic_impl sh h R * |> R), emp; simpl.
    rewrite emp_sepcon. iSplit.
    - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx; simpl.
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
       SEP (weak_exclusive_mpred R && emp; lock_inv sh h R; P; lock_inv sh h R * P -* Q * R)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (|> Q).
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as ((((?, ?), ?), ?), ?); simpl.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; do 3 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
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
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    setoid_rewrite later_nonexpansive; rewrite approx_idem; auto.
  Qed.

  Lemma release_inv_simple: funspec_sub (snd release_spec) release_spec_inv.
  Proof.
    apply prove_funspec_sub.
    split; auto. intros. simpl in *. destruct x2 as ((((sh, h), R), P), Q). Intros.
    unfold rev_curry, tcurry. iIntros "H !>". iExists nil.
    iExists (@ptr_of atomic_impl h, |> Q), emp. simpl in *.
    rewrite emp_sepcon. iSplit.
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
        iAssert (|>FF) with "[H5 R HR]" as ">[]".
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
    rewrite emp_sepcon. iSplit.
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
      + iAssert (|>FF) with "[H5 R H3]" as ">[]".
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
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
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

  #[local] Hint Resolve self_part_exclusive : core.

  Lemma release_self : funspec_sub (snd release_spec) release_spec_self.
  Proof.
    apply prove_funspec_sub.
    split; auto. intros. simpl in *. destruct x2 as ((sh, h), R). Intros.
    unfold rev_curry, tcurry. iIntros "H !>". iExists nil.
    destruct h as ((v, N), g).
    iExists (v, emp), emp. simpl in *.
    rewrite emp_sepcon. iSplit.
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
    rewrite !sepcon_emp. iDestruct "H" as "(_ & % & % & H1 & HP & R)".
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
    - iAssert (|>FF) with "[R HP HR H2]" as ">[]".
      iNext; iApply "R"; iFrame; iSplit; auto.
    - iAssert (|>FF) with "[H2 inv]" as ">[]".
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
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    f_equal.
    setoid_rewrite (@lock_inv_super_non_expansive atomic_impl); do 2 f_equal.
    rewrite !approx_sepcon approx_idem; auto.
  Qed.
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as (((?, ?), ?), ?); simpl.
    unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  Qed.

  Lemma lock_inv_share : forall sh h R, lock_inv sh h R |-- !!(sh <> Share.bot /\ isptr (ptr_of h)).
  Proof.
    intros; destruct h as ((?, ?), ?); unfold lock_inv; simpl; Intros; entailer!.
  Qed.

  Lemma freelock_self : funspec_sub (snd freelock_spec) freelock_spec_self.
  Proof.
    eapply funspec_sub_trans; [apply freelock_inv|].
    apply prove_funspec_sub.
    split; auto; intros ? (((sh1, sh2), h), R) ?; Intros; simpl.
    iIntros "H !>".
    iExists nil, (h, self_part sh2 h * R, emp), emp.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl.
    rewrite !emp_sepcon !sepcon_emp.
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
      rewrite emp_sepcon; apply andp_left2; auto.
  Qed.

End PROOFS.

Notation selflock R sh h := (self_part sh h * R).

#[export] Hint Resolve self_part_exclusive : core.
#[export] Hint Resolve lock_inv_share : saturate_local.

Ltac lock_props ::= match goal with |-context[weak_exclusive_mpred ?P && _] => sep_apply (exclusive_weak_exclusive P); [auto with share | try timeout 20 cancel]
  | |-context[weak_exclusive_mpred' ?P && _] => sep_apply (exclusive_weak_exclusive' P); [auto with share | try timeout 20 cancel] end.

(* when interacting with atomic updates, we need to unfold the definition of lock_inv and split its pieces *)
Ltac unfold_lock_inv := match goal with |-context[lock_inv _ ?h _] =>
  unfold lock_inv; simpl; let v := fresh "v" in let N := fresh "N" in let g := fresh "g" in destruct h as ((v, N), g) end.
