Require Import VST.concurrency.conclib.
Require Import VST.floyd.library.

Section lock_specs.

Context `{!heapGS Σ}.

(* lock invariants should be exclusive *)
Class lock_impl := { t_lock : type; lock_handle : Type; ptr_of : lock_handle -> val;
  lock_inv : Qp -> lock_handle -> mpred -> mpred;
  lock_inv_nonexpansive :: forall sh h, NonExpansive (lock_inv sh h);
  lock_inv_share_join : forall sh1 sh2 h R,
    lock_inv sh1 h R ∗ lock_inv sh2 h R ⊣⊢ lock_inv (sh1 ⋅ sh2) h R;
(*  lock_inv_exclusive : forall sh h R, exclusive_mpred (lock_inv sh h R); *)
  lock_inv_isptr : forall sh h R, lock_inv sh h R ⊢ ⌜isptr (ptr_of h)⌝ }.

  Context {LI : lock_impl}.

  Notation InvType := Mpred.

  (* R should be able to take the lock_handle as an argument, with subspecs for plain and selflock *)
  Program Definition makelock_spec :=
    TYPE (ProdType (ConstType globals) (DiscreteFunType lock_handle InvType)) WITH gv: _, R : _
    PRE [ ]
       PROP ()
       PARAMS () GLOBALS (gv)
       SEP (mem_mgr gv)
    POST [ tptr t_lock ] ∃ h,
       PROP ()
       RETURN (ptr_of h)
       SEP (mem_mgr gv; lock_inv 1 h (R h)).
  Next Obligation.
  Proof.
    intros ? (?, ?) (?, ?) ([=] & HR) ?; simpl in *; subst; done.
  Qed.
  Next Obligation.
  Proof.
    intros ? (?, ?) (?, ?) ([=] & HR) ?; simpl in *; subst.
    by repeat f_equiv.
  Qed.

  Program Definition freelock_spec :=
    TYPE (ProdType (ProdType (ConstType _) InvType) Mpred)
    WITH h : _, R : _, P : _
    PRE [ tptr t_lock ]
     PROP ()
     PARAMS (ptr_of h)
     SEP (lock_inv 1 h R; P; <affine> (P ∗ lock_inv 1 h R ∗ R -∗ False))
   POST[ tvoid ]
     PROP ()
     LOCAL ()
     SEP (P).
  Next Obligation.
  Proof.
    intros ? ((?, ?), ?) ((?, ?), ?) (([=] & HR) & HP) ?; simpl in *; subst.
    by repeat f_equiv.
  Qed.
  Next Obligation.
  Proof.
    intros ? ((?, ?), ?) ((?, ?), ?) (([=] & HR) & HP) ?; simpl in *; subst.
    by repeat f_equiv.
  Qed.

  Program Definition freelock_spec_simple :=
    TYPE (ProdType (ConstType _) InvType)
    WITH h : _, R : _
    PRE [ tptr t_lock ]
     PROP ()
     PARAMS (ptr_of h)
     SEP (<affine> (R ∗ R -∗ False); lock_inv 1 h R; R)
   POST[ tvoid ]
     PROP ()
     LOCAL ()
     SEP (R).
  Next Obligation.
  Proof.
    intros ? (?, ?) (?, ?) ([=] & HR) ?; simpl in *; subst.
    by repeat f_equiv.
  Qed.
  Next Obligation.
  Proof.
    intros ? (?, ?) (?, ?) ([=] & HR) ?; simpl in *; subst.
    by repeat f_equiv.
  Qed.

  Lemma freelock_simple : funspec_sub freelock_spec freelock_spec_simple.
  Proof.
    unfold funspec_sub; simpl.
    split; first done; intros (h, R) ?; Intros.
    iIntros "(? & ? & H) !>"; iExists (h, R, R), emp.
    iSplit; last by iPureIntro; entailer!.
    repeat (iSplit; first done).
    rewrite /SEPx /= /LOCALx /argsassert2assert /=; monPred.unseal.
    repeat (iSplit; first done).
    iDestruct "H" as "(? & HR & $ & $ & _)".
    repeat (iSplit; last done).
    iApply (bi.affinely_mono with "HR").
    iIntros "HR (? & ? & ?)"; iApply ("HR" with "[$]").
  Qed.

  Program Definition acquire_spec :=
    TYPE (ProdType (ConstType _) InvType)
    WITH sh : _, h : _, R : _
    PRE [ tptr t_lock ]
       PROP ()
       PARAMS (ptr_of h)
       SEP (lock_inv sh h R)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (lock_inv sh h R; R).
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

  Program Definition release_spec :=
    TYPE (ProdType (ProdType (ProdType (ConstType _) InvType) Mpred) Mpred)
    WITH sh : _, h : _, R : _, P : _, Q : _
    PRE [ tptr t_lock ]
       PROP ()
       PARAMS (ptr_of h)
       SEP (<affine> (R ∗ R -∗ False); ▷ lock_inv sh h R; P; lock_inv sh h R ∗ P -∗ Q ∗ R)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (Q).
  Next Obligation.
  Proof.
    intros ? ((((?, ?), ?), ?), ?) ((((?, ?), ?), ?), ?) ((([=] & HR) & HP) & HQ) ?; simpl in *; subst.
    by repeat f_equiv.
  Qed.
  Next Obligation.
  Proof.
    intros ? ((((?, ?), ?), ?), ?) ((((?, ?), ?), ?), ?) ((([=] & HR) & HP) & HQ) ?; simpl in *; subst.
    by repeat f_equiv.
  Qed.

  Program Definition release_spec_simple :=
    TYPE (ProdType (ConstType _) InvType)
    WITH sh : _, h : _, R : _
    PRE [ tptr t_lock ]
       PROP ()
       PARAMS (ptr_of h)
       SEP (<affine> (R ∗ R -∗ False); lock_inv sh h R; R)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (lock_inv sh h R).
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

  Lemma release_simple : funspec_sub release_spec release_spec_simple.
  Proof.
    unfold funspec_sub; simpl.
    split; first done; intros ((sh, h), R) ?; Intros.
    iIntros "(? & ? & H) !>"; iExists (sh, h, R, R, lock_inv sh h R), emp.
    iSplit; last by iPureIntro; entailer!.
    repeat (iSplit; first done).
    rewrite /SEPx /= /LOCALx /argsassert2assert /=; monPred.unseal.
    repeat (iSplit; first done).
    iDestruct "H" as "(? & HR & $ & $ & _)".
    iFrame; auto.
  Qed.

  Context (Z : Type) `{!externalGS Z Σ}.

  Definition concurrent_specs (cs : compspecs) (ext_link : string -> ident) :=
    (ext_link "spawn"%string, spawn_spec) ::
    (ext_link "makelock"%string, makelock_spec) ::
    (ext_link "freelock"%string, freelock_spec) ::
    (ext_link "acquire"%string, acquire_spec) ::
    (ext_link "release"%string, release_spec) ::
    nil.

  Definition concurrent_ext_spec (cs : compspecs) (ext_link : string -> ident) :=
    add_funspecs_rec Z
      ext_link
      (ok_void_spec Z).(OK_spec)
      (concurrent_specs cs ext_link).

  Definition Concurrent_Espec cs ext_link :=
    Build_OracleKind
      Z
      (concurrent_ext_spec cs ext_link).

End lock_specs.

#[export] Hint Resolve lock_inv_isptr : saturate_local.
#[export] Hint Resolve data_at_exclusive data_at__exclusive field_at_exclusive field_at__exclusive : core.

Ltac lock_props := match goal with |-context[<affine> (?P ∗ ?P -∗ False)] => rewrite -(exclusive_weak_exclusive P);
  [rewrite bi.affinely_emp bi.emp_sep | auto with share] end.
