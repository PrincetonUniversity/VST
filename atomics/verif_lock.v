Require Import VST.concurrency.conclib.
Require Import VST.concurrency.ghosts.
Require Import VST.floyd.library.
Require Import VST.atomics.SC_atomics.
Require Import VST.atomics.general_atomics.
Require Import VST.atomics.lock.

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
    ATOMIC TYPE (rmaps.ConstType (val * globals)) OBJ n INVS empty top
    WITH p, gv
    PRE [ tptr t_lock ]
       PROP (is_pointer_or_null p)
       PARAMS (p) GLOBALS (gv)
       SEP (mem_mgr gv) | (atomic_int_at Ews (vint n) p)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (mem_mgr gv) | (atomic_int_at Ews (vint 0) p).


  Definition Gprog : funspecs :=
    ltac:(with_library prog [make_atomic_spec; atom_store_spec; atom_CAS_spec;
                             free_atomic_spec; makelock_spec; freelock_spec;
                             release_spec]).

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

End PROOFS.
