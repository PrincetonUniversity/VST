Require Import VST.concurrency.conclib.
Require Import VST.concurrency.ghosts.
Require Import VST.concurrency.invariants.
Require Import VST.floyd.library.
Require Import VST.atomics.SC_atomics.
Require Import VST.atomics.general_atomics.
Require Import VST.atomics.lock.

Section PROOFS.

Context {inv_names0 : invG}.

Definition funspec_sub (f1 f2 : funspec): Prop :=
match f1 with
| mk_funspec tpsig1 cc1 A1 P1 Q1 _ _ =>
    match f2 with
    | mk_funspec tpsig2 cc2 A2 P2 Q2 _ _ =>
        (tpsig1=tpsig2 /\ cc1=cc2) /\
        forall ts2 x2 (gargs:argsEnviron),
        ((!! (argsHaveTyps(snd gargs)(fst tpsig1)) && P2 ts2 x2 gargs)
         |-- (|={⊤}=> (EX ts1:_,  EX x1:_, EX F:_,
                           (F * (P1 ts1 x1 gargs)) &&
                               (!! (forall rho',
                                           ((!!(ve_of rho' = Map.empty (Values.block * type))) &&
                                                 (F * (Q1 ts1 x1 rho')))
                                         |-- |={⊤}=> (Q2 ts2 x2 rho'))))))%I
    end
end.


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

  Definition makelock_spec :=
    DECLARE _makelock
    WITH gv: globals
    PRE []
       PROP ()
       PARAMS () GLOBALS (gv)
       SEP (mem_mgr gv)
    POST [ tptr t_lock ] EX p: val,
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
    ATOMIC TYPE (rmaps.ConstType _) INVS empty top
    WITH p, gv
    PRE [ tptr t_lock ]
       PROP ()
       PARAMS (p) GLOBALS (gv)
       SEP (mem_mgr gv) | (atomic_int_at Ews (vint 1) p)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (mem_mgr gv) | (atomic_int_at Ews (vint 0) p).

  Program Definition acquire_spec :=
    DECLARE _acquire
    ATOMIC TYPE (rmaps.ConstType _) OBJ l INVS empty top
    WITH p, gv
    PRE [ tptr t_lock ]
       PROP ()
       PARAMS (p) GLOBALS (gv)
       SEP (mem_mgr gv) | ((!! (l = true) && atomic_int_at Ews (vint 0) p) ||
                           (!! (l = false) && atomic_int_at Ews (vint 1) p))
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (mem_mgr gv) | (!! (l = true) && atomic_int_at Ews (vint 1) p).

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
    entailer !.
  Qed.

  Lemma body_freelock: semax_body Vprog Gprog f_freelock freelock_spec.
  Proof.
    start_function.
    Intros v.
    assert_PROP (is_pointer_or_null p) by entailer.
    forward_call (p).
    - Exists v. cancel.
    - entailer !.
  Qed.

  Lemma body_release: semax_body Vprog Gprog f_release release_spec.
  Proof.
    start_function.
    forward_call (p, (vint 0), top: coPset, empty: coPset, Q, inv_names).
    - assert (Frame = [mem_mgr gv]); subst Frame; [ reflexivity | clear H].
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
    forward.
    forward_loop (PROP ( )
                       LOCAL (temp _b (vint 0); lvar _expected tint v_expected;
                              gvars gv; temp _lock p)
                       SEP (data_at Tsh tint (vint 0) v_expected;
                            atomic_shift
                              (λ l : bool,
                                  !! (l = true) && atomic_int_at Ews (vint 0) p
                                  || !! (l = false) && atomic_int_at Ews (vint 1) p) ∅ ⊤
                              (λ (l : bool) (_ : ()),
                                fold_right_sepcon [!! (l = true) && atomic_int_at Ews (vint 1) p])
                              (λ _ : (), Q); mem_mgr gv)).
    - entailer !.
    - forward_call
        (p , Tsh, v_expected, (vint 0), (vint 1), top : coPset,
            empty : coPset,
              fun v':val =>
                if (eq_dec v' (vint 0)) then Q else
                  (atomic_shift
                     (λ l : bool,
                         !! (l = true) && atomic_int_at Ews (vint 0) p
                         || !! (l = false) && atomic_int_at Ews (vint 1) p) ∅ ⊤
                     (λ (l : bool) (_ : ()),
                       fold_right_sepcon [!! (l = true) && atomic_int_at Ews (vint 1) p]) (λ _ : (), Q)), inv_names).
      + assert (Frame = [mem_mgr gv]); subst Frame; [ reflexivity | clear H].
        simpl fold_right_sepcon. cancel.
        iIntros ">AS". iExists Ews.
        iDestruct "AS" as (x) "[[a | a] H]".
        * iDestruct "H" as "[_ H]". iDestruct "a" as (a) "b".
          iExists (vint 0). iModIntro. iSplitL "b".
          -- iSplit; auto.
          -- iSpecialize ("H" $! tt). iIntros "AA". iApply "H".
             destruct (eq_dec (vint 0) (vint 0)). 2: exfalso; now apply n.
             iSplit; [iSplit|]; auto.
        * iExists (vint 1). iModIntro. destruct (eq_dec (vint 1) (vint 0)).
          1: inversion e. do 2 rewrite sepcon_andp_prop'. iSplit.
          -- iPureIntro. apply writable_Ews.
          -- iDestruct "a" as (Hx) "a". iSplitL "a". 1: auto. iIntros "AS".
             iMod ("H" with "[AS]").
             { iRight; iFrame; auto. }
             iFrame; auto.
      + Intros r. destruct (eq_dec r (vint 0)).
        * forward_if. 1: exfalso; apply H'; auto. forward. entailer !.
        * forward_if. 2: inversion H. forward. entailer !.
  Qed.

  Definition lock_inv (l: val) (R: mpred): mpred :=
    EX i, invariant i (atomic_int_at Ews (vint 0) l * R || atomic_int_at Ews (vint 1) l).

  Lemma nonexpansive_lock_inv : forall p, nonexpansive (lock_inv p).
  Proof.
    intros.
    unfold lock_inv.
    apply @exists_nonexpansive.
    intros i.
    apply invariant_nonexpansive2.
    apply @disj_nonexpansive.
    - apply @sepcon_nonexpansive.
      + apply _.
      + apply const_nonexpansive.
      + apply identity_nonexpansive.
    - apply const_nonexpansive.
  Qed.

  Program Definition makelock_spec2: funspec :=
    mk_funspec
      (nil, tptr t_lock)
      cc_default
      (rmaps.ProdType (rmaps.ConstType (globals)) rmaps.Mpred)
      (fun _ x =>
         match x with
         | (gv, R) =>
             PROP ()
                  PARAMS () GLOBALS (gv)
                  SEP (mem_mgr gv)
         end)%argsassert
      (fun _ x =>
         match x with
         | (gv, R) =>
             EX v, PROP ()
                   LOCAL ()
                   SEP (mem_mgr gv; lock_inv v R)
         end)
      _
      _
  .
  Next Obligation.
    intros. simpl in *.
    apply (nonexpansive_super_non_expansive
             (fun _f => (EX x0 : val, (PROP ( )  RETURN ( )
                                         SEP (mem_mgr x; lock_inv x0 _f)) rho))).
    replace (λ _f0 : mpred,
                EX x0 : val, (PROP ( )  RETURN ( ) SEP (mem_mgr x; lock_inv x0 _f0)) rho)
      with (λ _f0 : mpred,
               (PROP ( )  RETURN ( ) SEP (mem_mgr x; EX x0, lock_inv x0 _f0)) rho).
    - apply (PROP_LOCAL_SEP_nonexpansive
             nil
             nil
             ((fun _f : mpred => mem_mgr x) :: (fun _f => EX x0, lock_inv x0 _f) :: nil));
        constructor.
      + apply const_nonexpansive.
      + constructor.
        * apply @exists_nonexpansive. apply nonexpansive_lock_inv.
        * constructor.
    - extensionality f. unfold PROPx, LOCALx, SEPx. simpl. normalize.
      f_equal. extensionality y. normalize.
  Qed.

  Lemma makelock_funspec_sub: funspec_sub (snd makelock_spec) makelock_spec2.
  Proof.
    split; auto. intros. simpl in *. destruct x2 as [gv R]. Intros.
    iIntros "H !>". iExists nil, gv, emp. rewrite emp_sepcon. iSplit; auto.
    iPureIntro. intros. Intros. rewrite emp_sepcon. Intros x.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx; simpl. Intros.
    rewrite <- !exp_andp2. normalize. rewrite <- exp_sepcon2.
    iIntros "(% & H1 & H2)". iSplitL "H1"; auto. iExists x. rewrite sepcon_emp.
    unfold lock_inv. iApply make_inv. 2: iApply "H2". apply orp_right2. cancel.
  Qed.

  Definition acquire_arg_type: rmaps.TypeTree := rmaps.ProdType (rmaps.ConstType (val * globals)) rmaps.Mpred.

  Definition acquire_pre: val * globals * mpred -> argsEnviron -> mpred :=
    fun args =>
      match args with
      | (v, gv, R) =>
          PROP ()
               PARAMS (v) GLOBALS (gv)
               SEP (mem_mgr gv; lock_inv v R)
      end%argsassert.

  Notation acquire_post :=
    (fun args =>
       match args with
       | (v, gv, R) =>
           PROP ()
                LOCAL ()
                SEP (mem_mgr gv; lock_inv v R; |> R)
       end).

  Lemma NP_acquire_pre: @args_super_non_expansive acquire_arg_type (fun _ => acquire_pre).
  Proof.
    hnf.
    intros.
    destruct x as [[v gv] R]; simpl in *.
    unfold PROPx. simpl. do 2 rewrite approx_andp. f_equal.
    unfold LAMBDAx. do 2 rewrite approx_andp. f_equal.
    unfold GLOBALSx, LOCALx. simpl. do 2 rewrite approx_andp. f_equal.
    unfold argsassert2assert, SEPx. simpl. do 2 rewrite sepcon_emp.
    do 2 rewrite approx_sepcon. f_equal.
    apply nonexpansive_super_non_expansive. apply nonexpansive_lock_inv.
  Qed.

  Lemma NP_acquire_post: @super_non_expansive acquire_arg_type (fun _ => acquire_post).
  Proof.
    hnf.
    intros.
    destruct x as [[v gv] R]; simpl in *.
    apply (nonexpansive_super_non_expansive
             (fun R => (PROP ()  LOCAL ()  SEP (mem_mgr gv; lock_inv v R; |> R)) rho)).
    apply (PROP_LOCAL_SEP_nonexpansive
             nil
             nil
             ((fun R: mpred => mem_mgr gv) :: (fun R => lock_inv v R) :: (fun R => |> R) :: nil));
      constructor.
    - apply const_nonexpansive.
    - constructor.
      + apply nonexpansive_lock_inv.
      + constructor; [apply later_nonexpansive' | constructor].
  Qed.

  Definition acquire_spec2: funspec := mk_funspec
                                        (tptr t_lock :: nil, tvoid)
                                        cc_default
                                        acquire_arg_type
                                        (fun _ => acquire_pre)
                                        (fun _ => acquire_post)
                                        NP_acquire_pre
                                        NP_acquire_post.

  Hypothesis atomic_int_timeless : forall sh v p, Timeless (atomic_int_at sh v p).
  Existing Instance atomic_int_timeless.

  Lemma acquire_funspec_sub: funspec_sub (snd acquire_spec) acquire_spec2.
  Proof.
    split; auto. intros. simpl in *. destruct x2 as [[v gv] R]. Intros.
    unfold rev_curry, tcurry. iIntros "H !>". iExists nil.
    iExists (((v, gv), lock_inv v R * |> R), inv_names0), emp. simpl in *.
    rewrite emp_sepcon. iSplit.
    - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx; simpl. normalize.
      iDestruct "H" as "(% & H1 & H2 & H3)". iSplit.
      + iPureIntro. auto.
      + iSplit; auto. unfold argsassert2assert. iSplitL "H3"; auto. unfold lock_inv.
        iDestruct "H3" as (i) "# H". unfold atomic_shift. iAuIntro. unfold atomic_acc; simpl.
        iMod (inv_open with "H") as "[inv Hclose]". set_solver.
        rewrite later_orp. rewrite later_sepcon.
        iDestruct "inv" as "[[> H1 R]|> H1]".
        * iApply fupd_mask_intro; try set_solver. iIntros "H2". iExists true.
          normalize. iSplitL "H1".
          -- iLeft; auto.
          -- iSplit.
             ++ iIntros "[H1 | [% H3]]". 2: exfalso; inversion H1.
                 iMod "H2". iApply "Hclose". iLeft; iFrame; auto.
             ++ iIntros (_) "H1". iMod "H2". iExists i. iFrame "#". iFrame. iApply "Hclose".
                iRight. iFrame. auto.
        * iExists false. iApply fupd_mask_intro; try set_solver. iIntros "H2". iSplitL "H1".
          -- iRight; iFrame; auto.
          -- iSplit.
             ++ iIntros "[[% H1] | [% H1]]". 1: inversion H1. iMod "H2". iApply "Hclose".
                iRight. iFrame; auto.
             ++ iIntros (_) "[[% ?] _]"; discriminate.
    - iPureIntro. iIntros (rho') "[% [_ H]]". iIntros "!>".
      unfold PROPx, LOCALx, SEPx; simpl. normalize. rewrite sepcon_comm. auto.
  Qed.

  Definition release_arg_type: rmaps.TypeTree :=
    rmaps.ProdType (rmaps.ConstType (val * globals)) rmaps.Mpred.

  Definition release_pre: val * globals * mpred -> argsEnviron -> mpred :=
    fun args =>
      match args with
      | (v, gv, R) =>
          PROP ()
               PARAMS (v) GLOBALS (gv)
               SEP (mem_mgr gv; weak_exclusive_mpred R && emp; lock_inv v R; R)
      end%argsassert.

  Notation release_post :=
    (fun args =>
       match args with
       | (v, gv, R) =>
           PROP ()
                LOCAL ()
                SEP (mem_mgr gv; lock_inv v R)
       end).

  Lemma NP_release_pre: @args_super_non_expansive release_arg_type (fun _ => release_pre).
  Proof.
    hnf.
    intros.
    destruct x as [[v gv] R]; simpl in *.
    unfold PROPx. simpl. do 2 rewrite approx_andp. f_equal.
    unfold LAMBDAx. simpl. do 2 rewrite approx_andp. f_equal.
    unfold GLOBALSx, LOCALx. simpl. do 2 rewrite approx_andp. f_equal.
    unfold argsassert2assert. simpl. unfold SEPx; simpl. do 2 rewrite sepcon_emp.
    repeat rewrite -> approx_sepcon. do 2 f_equal; [|f_equal].
    - apply (nonexpansive_super_non_expansive (fun R => weak_exclusive_mpred R && emp))%logic.
      apply (conj_nonexpansive (fun R => weak_exclusive_mpred R)%logic).
      + apply exclusive_mpred_nonexpansive.
      + apply const_nonexpansive.
    - apply (nonexpansive_super_non_expansive). apply nonexpansive_lock_inv.
    - remember (compcert_rmaps.RML.R.approx
                  n (compcert_rmaps.RML.R.approx n R)).
      rewrite <- (compcert_rmaps.RML.approx_oo_approx n). subst. reflexivity.
  Qed.

  Lemma NP_release_post: @super_non_expansive release_arg_type (fun _ => release_post).
  Proof.
    hnf.
    intros.
    destruct x as [[v gv] R]; simpl in *.
    apply (nonexpansive_super_non_expansive
             (fun R => (PROP ()  LOCAL ()  SEP (mem_mgr gv; lock_inv v R)) rho)).
    apply (PROP_LOCAL_SEP_nonexpansive
             nil
             nil
             ((fun R: mpred => mem_mgr gv) :: (fun R => lock_inv v R) :: nil)); constructor.
    - apply const_nonexpansive.
    - constructor; [apply nonexpansive_lock_inv | constructor].
  Qed.

  Definition release_spec2: funspec := mk_funspec
                                         (*((_lock OF tptr Tvoid)%formals :: nil, tvoid)*)
                                         ((tptr t_lock) :: nil, tvoid)
                                         cc_default
                                         release_arg_type
                                         (fun _ => release_pre)
                                         (fun _ => release_post)
                                         NP_release_pre
                                         NP_release_post.

  Lemma release_funspec_sub: funspec_sub (snd release_spec) release_spec2.
  Proof.
    split; auto. intros. simpl in *. destruct x2 as [[v gv] R]. Intros.
    unfold rev_curry, tcurry. iIntros "H !>". iExists nil.
    iExists (((v, gv), lock_inv v R), inv_names0), emp. simpl in *.
    rewrite emp_sepcon. iSplit.
    - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx; simpl. normalize.
      iDestruct "H" as "(% & H1 & H2 & H3 & H4 & H5)". iSplit.
      + iPureIntro. auto.
      + iSplit; auto. unfold argsassert2assert. iSplitR "H2"; auto. unfold lock_inv.
        iDestruct "H4" as (i) "#H". unfold atomic_shift. iAuIntro. unfold atomic_acc; simpl.
        iMod (inv_open with "H") as "[inv Hclose]". set_solver.
        rewrite later_orp. rewrite later_sepcon.
        iDestruct "inv" as "[[> H2 R]|> H2]".
        * iAssert (|>FF) with "[H3 H5 R]" as ">[]".
          iNext; iApply weak_exclusive_conflict; iFrame; iFrame.
        * iExists tt. iApply fupd_mask_intro; try set_solver. iIntros "H4".
          iSplitL "H2"; auto. iSplit.
          -- iIntros "H2". iFrame. iMod "H4". iApply "Hclose". iRight. iFrame. auto.
          -- iIntros (_) "H2". iFrame. iExists i. iFrame "#". iMod "H4". iApply "Hclose".
             iLeft. iFrame. auto.
    - iPureIntro. iIntros (rho') "[% [_ H]]". iIntros "!>".
      unfold PROPx, LOCALx, SEPx; simpl. normalize. rewrite sepcon_comm. auto.
  Qed.

  Program Definition freelock_spec2: funspec :=
    mk_funspec
      ((tptr t_lock) :: nil, tvoid)
      cc_default
      (rmaps.ProdType (rmaps.ConstType val) rmaps.Mpred)
      (fun _ x =>
         match x with
         | (v,R) =>
             PROP ()
                  PARAMS (v) GLOBALS()
                  SEP (weak_exclusive_mpred R && emp; lock_inv v R; R)
         end)%argsassert
      (fun _ x =>
         match x with
         | (v, R) =>
             PROP ()
                  LOCAL ()
                  SEP (R)
         end)
      _
      _.
  Next Obligation.
    intros. simpl in *. rename x into v. rename _f into R.
    apply (nonexpansive_super_non_expansive
             (fun R => (PROP () PARAMS(v) GLOBALS()
                     SEP (weak_exclusive_mpred R && emp; lock_inv v R; R))%argsassert gargs)).
    unfold PARAMSx, GLOBALSx, SEPx, PROPx, LOCALx, argsassert2assert. simpl.
    apply @conj_nonexpansive.
    - apply const_nonexpansive.
    - apply @conj_nonexpansive.
      + apply const_nonexpansive.
      + apply @conj_nonexpansive.
        * apply const_nonexpansive.
        * apply sepcon_nonexpansive.
          -- apply @conj_nonexpansive.
             ++ apply exclusive_mpred_nonexpansive.
             ++ apply const_nonexpansive.
          -- apply sepcon_nonexpansive.
             ++ apply nonexpansive_lock_inv.
             ++ apply sepcon_nonexpansive.
                ** apply identity_nonexpansive.
                ** apply const_nonexpansive.
  Qed.
  Next Obligation.
    intros. rename x into v. rename _f into R. simpl in *.
    apply (nonexpansive_super_non_expansive
             (fun R => (PROP ()  LOCAL ()  SEP (R)) rho)).
    apply (PROP_LOCAL_SEP_nonexpansive
             nil
             nil
             ((fun R => R) :: nil)); constructor.
    - apply identity_nonexpansive.
    - constructor.
  Qed.

  Lemma freelock_funspec_sub: funspec_sub (snd freelock_spec) freelock_spec2.
  Proof.
    split; auto. intros. simpl in *. destruct x2 as [p R]. Intros.
    iIntros "H !>". iExists nil, p, R. iSplit.
    - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx; simpl. unfold argsassert2assert.
      rewrite !sepcon_emp. iDestruct "H" as "(_ & % & % & H1 & H2 & R)". iSplitL "R"; auto.
      do 3 (iSplit; auto). unfold lock_inv. iDestruct "H2" as "(% & H2)". admit.
    - iPureIntro. intros. Intros.
      unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx; simpl. Intros.
      normalize. iIntros "H !>". auto.
  Abort.

End PROOFS.
