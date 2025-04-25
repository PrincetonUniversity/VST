Require Import VST.concurrency.conclib.
Require Import VSTlib.locks.
Require Import VSTlib.spec_malloc.
Require Import iris_ora.logic.cancelable_invariants.

Definition lock_handle : Type := val * namespace * gname.
Definition ptr_of (h: lock_handle) : val := let '(v, i, g) := h in v.

 (* We can use self_part sh h * R instead of selflock sh h R. *)
Definition self_part `{!VSTGS OK_ty Σ, !cinvG Σ} sh (h : lock_handle) := let '(v, i, g) := h in cinv_own g sh.

Section GFUNCTORS.

Context `{!VSTGS OK_ty Σ, !cinvG Σ}.


Class lockAPD := {
  t_lock : type := Tstruct _atom_int noattr;
  inv_for_lock: forall (v: val) (R: mpred), mpred;
  inv_for_lock_nonexpansive : forall v, NonExpansive (inv_for_lock v)
}.

#[export] Existing Instance inv_for_lock_nonexpansive.

Definition lock_inv {L: lockAPD} (sh: Qp) (h: lock_handle)  (R: mpred) :=
   let '(v, i, g) := h in ⌜ isptr v⌝ ∧ cinv i g (inv_for_lock v R) ∗ cinv_own g sh.

#[export] Instance lock_inv_nonexpansive {L: lockAPD}: 
  ∀ (sh : Qp) (h : val * namespace * gname) (n : nat),
  Proper (dist n ==> dist n) (lock_inv sh h).
Proof. unfold lock_inv. solve_proper. Qed.

Lemma self_part_eq {L: lockAPD}: forall sh1 sh2 h R, 
    lock_inv sh1 h (self_part sh2 h ∗ R) ∗ self_part sh2 h ⊣⊢
    lock_inv sh1 h (self_part sh2 h ∗ R) ∗ lock_inv sh2 h (self_part sh2 h ∗ R).
  Proof.
    intros.
    simpl; unfold lock_inv; destruct h as ((?, ?), ?).
    iSplit.
    - iIntros "((#$ & #$ & $) & $)".
    - iIntros "(($ & $ & $) & (_ & _ & $))".
  Qed.

Lemma lock_inv_share_join {L: lockAPD} : forall sh1 sh2 h R,
    lock_inv sh1 h R ∗ lock_inv sh2 h R ⊣⊢ lock_inv (sh1 ⋅ sh2) h R.
  Proof.
    unfold lock_inv.
    intros ?? ((?, ?), ?) ?.
    rewrite /cinv_own own_op; iSplit.
    - iIntros "(($ & $ & $) & (_ & _ & $))".
    - iIntros "(#$ & #$ & $ & $)".
  Qed.

Section lock_specs.

  Context {M: MallocAPD} {L : lockAPD}.

  Definition selflock R sh h := self_part sh h ∗ R.

  Lemma lock_inv_isptr : forall sh h R, lock_inv sh h R ⊢ ⌜isptr (ptr_of h)⌝.
  Proof. intros. destruct h as [[? ?] ?]; simpl. entailer!!. Qed.

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
    unfold lock_inv. repeat f_equiv.
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
    iSplit; first done.
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
    iSplit; first done.
    iSplit; last by iPureIntro; entailer!.
    repeat (iSplit; first done).
    rewrite /SEPx /= /LOCALx /argsassert2assert /=; monPred.unseal.
    repeat (iSplit; first done).
    iDestruct "H" as "(? & HR & $ & $ & _)".
    iFrame; auto.
  Qed.

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
  iSplit; first done.
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
  iSplit; first done.
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

Opaque lock_handle.
Opaque ptr_of.
Opaque lock_inv.
Opaque self_part.
Arguments ptr_of : simpl never.
Arguments lock_inv : simpl never.

Definition LockASI:funspecs := [
   (_makelock, makelock_spec);
   (_freelock, freelock_spec);
   (_acquire, acquire_spec);
   (_release, release_spec)
].

End lock_specs.
End GFUNCTORS.

Ltac lock_props := match goal with |-context[<affine> (?P ∗ ?P -∗ False)] => rewrite -(exclusive_weak_exclusive P);
  [rewrite bi.affinely_emp ?bi.emp_sep ?bi.sep_emp | auto with share] end.


#[export] Hint Resolve lock_inv_isptr : saturate_local.

