Require Import VST.concurrency.conclib.
Require Import VST.concurrency.ghosts.
Require Import VST.floyd.library.
Require Import VST.atomics.SC_atomics.
Require Import VST.atomics.general_atomics.
Require Import VST.atomics.lock.

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

Section PROOFS.

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
       SEP (mem_mgr gv; atomic_int_at Ews (vint 0) p).

  Definition freelock_spec :=
    DECLARE _freelock
    WITH p : val
    PRE [ tptr t_lock ]
     PROP (is_pointer_or_null p)
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
       PROP (is_pointer_or_null p)
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
       PROP (is_pointer_or_null p)
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
    forward_call (vint 0).
    Intros p.
    forward.
    Exists p.
    entailer !.
  Qed.

  Lemma body_freelock: semax_body Vprog Gprog f_freelock freelock_spec.
  Proof.
    start_function.
    forward_call (p).
    entailer !.
  Qed.

  Lemma body_release: semax_body Vprog Gprog f_release release_spec.
  Proof.
    start_function.
    forward_call (p, (vint 0), top: coPset, empty: coPset, Q, inv_names).
    - assert (Frame = [mem_mgr gv]); subst Frame; [ reflexivity | clear H0].
      simpl fold_right_sepcon. cancel.
      iIntros "AS".
      unfold atomic_shift, ashift.
      iDestruct "AS" as (P) "[P AS]".
      iMod ("AS" with "P") as (x) "[a [_ H]]".
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
    start_function. clear H.
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
        iIntros "AS". iExists Ews.
        unfold atomic_shift at 1. unfold ashift.
        iDestruct "AS" as (P) "[P AS]".
        iDestruct (cored_dup with "AS") as "[AS AS1]".
        iMod ("AS" with "P") as (x) "[[a | a] H]".
        * iDestruct "AS1" as "[_ AS1]". iMod (cored_emp with "AS1") as "_".
          iDestruct "H" as "[_ H]". iDestruct "a" as (a) "b".
          iExists (vint 0). iModIntro. iSplitL "b".
          -- iSplit; auto.
          -- iSpecialize ("H" $! tt). iIntros "AA". iApply "H".
             destruct (eq_dec (vint 0) (vint 0)). 2: exfalso; now apply n.
             iSplit; [iSplit|]; auto.
        * iExists (vint 1). iModIntro. destruct (eq_dec (vint 1) (vint 0)).
          1: inversion e. do 2 rewrite sepcon_andp_prop'. iSplit.
          -- iPureIntro. apply writable_Ews.
          -- iDestruct "a" as (Hx) "a". iSplitL "a". 1: auto. iIntros "AS".
             iExists P. iMod ("H" with "[AS]").
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
    unfold lock_inv. iApply make_inv. 2: iApply "H2". apply orp_right1. cancel.
  Abort.

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
                SEP (mem_mgr gv; lock_inv v R; R)
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
             (fun R => (PROP ()  LOCAL ()  SEP (mem_mgr gv; lock_inv v R; R)) rho)).
    apply (PROP_LOCAL_SEP_nonexpansive
             nil
             nil
             ((fun R: mpred => mem_mgr gv) :: (fun R => lock_inv v R) :: (fun R => R) :: nil));
      constructor.
    - apply const_nonexpansive.
    - constructor.
      + apply nonexpansive_lock_inv.
      + constructor; [apply identity_nonexpansive | constructor].
  Qed.

  Definition acquire_spec2: funspec := mk_funspec
                                        (tptr t_lock :: nil, tvoid)
                                        cc_default
                                        acquire_arg_type
                                        (fun _ => acquire_pre)
                                        (fun _ => acquire_post)
                                        NP_acquire_pre
                                        NP_acquire_post.

  Lemma acquire_funspec_sub: funspec_sub (snd acquire_spec) acquire_spec2.
  Proof.
    split; auto. intros. simpl in *. destruct x2 as [[v gv] R]. Intros.
    unfold rev_curry, tcurry. iIntros "H !>". iExists nil.
    iExists (((v, gv), R), inv_names), emp. simpl in *. rewrite emp_sepcon. iSplit.
    - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx; simpl. normalize.
      iDestruct "H" as "(% & H1 & H2 & H3)". iSplit.
      + admit.
      + iSplit; auto. unfold argsassert2assert. iSplitL "H3"; auto. unfold lock_inv.
        iDestruct "H3" as (i) "H". iApply inv_atomic_shift; eauto.
        3: { rewrite <- (sepcon_emp (invariant i (atomic_int_at Ews (vint 0) v * R || atomic_int_at Ews (vint 1) v))).
             iApply "H". }
        * apply empty_subseteq.
        * rewrite later_orp. iIntros "[H|H]".
          -- iIntros "!>". iExists true. rewrite later_sepcon. normalize.
             iDestruct "H" as "(H1 & H2)". iSplitL "H1".
             ++ iApply orp_right1. 2: iApply "H1". admit.
             ++ iSplit.
                ** iIntros "[H1 | [% H3]]". 2: exfalso; inversion H1.
                   iIntros "!>". iApply orp_right1. apply derives_refl.
                   iSplitL "H1"; auto.
                ** iIntros (_) "(H1 & H3) !>". iSplitR "H2". 2: admit.
                   iApply orp_right2. apply derives_refl.
                   iApply now_later. admit.
          --

  Abort.


End PROOFS.
