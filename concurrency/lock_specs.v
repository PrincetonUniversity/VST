Require Import VST.veric.rmaps.
Require Import VST.concurrency.conclib.
Require Import VST.floyd.library.
Import FashNotation.

(* lock invariants should be exclusive *)
Class lock_impl := { t_lock : type; lock_handle : Type; ptr_of : lock_handle -> val;
  lock_inv : share -> lock_handle -> mpred -> mpred;
  lock_inv_nonexpansive : forall sh h, nonexpansive (lock_inv sh h);
  lock_inv_share_join : forall sh1 sh2 sh3 h R, sh1 <> Share.bot -> sh2 <> Share.bot ->
    sepalg.join sh1 sh2 sh3 -> lock_inv sh1 h R * lock_inv sh2 h R = lock_inv sh3 h R;
  lock_inv_exclusive : forall sh h R, exclusive_mpred (lock_inv sh h R);
  lock_inv_isptr : forall sh h R, lock_inv sh h R |-- !! isptr (ptr_of h) }.

Section lock_specs.

  Context {LI : lock_impl}.

  Lemma lock_inv_nonexpansive2 : forall {A} (P Q : A -> mpred) sh p x, (ALL x : _, |> (P x <=> Q x) |--
    |> lock_inv sh p (P x) <=> |> lock_inv sh p (Q x))%logic.
  Proof.
    intros.
    apply allp_left with x.
    eapply derives_trans, eqp_later1; apply later_derives.
    apply nonexpansive_entail; apply lock_inv_nonexpansive.
  Qed.

  Lemma lock_inv_super_non_expansive : forall sh h R n,
    compcert_rmaps.RML.R.approx n (lock_inv sh h R) = compcert_rmaps.RML.R.approx n (lock_inv sh h (compcert_rmaps.RML.R.approx n R)).
  Proof.
    intros; apply nonexpansive_super_non_expansive, lock_inv_nonexpansive.
  Qed.

  Notation InvType := Mpred.

  (* R should be able to take the lock_handle as an argument, with subspecs for plain and selflock *)
  Program Definition makelock_spec :=
    TYPE (ProdType (ConstType globals) (ArrowType (ConstType lock_handle) InvType)) WITH gv: _, R : _
    PRE [ ]
       PROP ()
       PARAMS () GLOBALS (gv)
       SEP (mem_mgr gv)
    POST [ tptr t_lock ] EX h,
       PROP ()
       RETURN (ptr_of h)
       SEP (mem_mgr gv; lock_inv Tsh h (R h)).
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
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; do 2 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    f_equal; apply lock_inv_super_non_expansive.
  Qed.

  Program Definition freelock_spec :=
    TYPE (ProdType (ProdType (ConstType _) InvType) Mpred)
    WITH h : _, R : _, P : _
    PRE [ tptr t_lock ]
     PROP ()
     PARAMS (ptr_of h)
     SEP (lock_inv Tsh h R; P; (P * lock_inv Tsh h R * R -* FF) && emp)
   POST[ tvoid ]
     PROP ()
     LOCAL ()
     SEP (P).
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as ((?, ?), ?); simpl.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; do 3 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    f_equal.
    { apply lock_inv_super_non_expansive. }
    f_equal.
    rewrite !approx_andp; f_equal.
    setoid_rewrite wand_nonexpansive; rewrite !approx_sepcon; do 2 f_equal; rewrite !approx_idem; auto.
    do 2 f_equal; apply lock_inv_super_non_expansive.
  Qed.
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as ((?, ?), ?); simpl.
    unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    reflexivity.
  Qed.

  Program Definition freelock_spec_simple :=
    TYPE (ProdType (ConstType _) InvType)
    WITH h : _, R : _
    PRE [ tptr t_lock ]
     PROP ()
     PARAMS (ptr_of h)
     SEP (weak_exclusive_mpred R && emp; lock_inv Tsh h R; R)
   POST[ tvoid ]
     PROP ()
     LOCAL ()
     SEP (R).
  Next Obligation.
  Proof.
    repeat intro.
    destruct x; simpl.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; do 3 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    f_equal.
    { rewrite !approx_andp; f_equal.
      apply exclusive_mpred_super_non_expansive. }
    f_equal. apply lock_inv_super_non_expansive.
  Qed.
  Next Obligation.
  Proof.
    repeat intro.
    destruct x; simpl.
    unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    reflexivity.
  Qed.

  Lemma freelock_simple : funspec_sub freelock_spec freelock_spec_simple.
  Proof.
    unfold funspec_sub; simpl.
    split; auto; intros ? (h, R) ?; Intros.
    eapply derives_trans, fupd_intro.
    Exists (nil : list Type) (h, R, R) emp; entailer!.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; entailer!.
    apply andp_right, andp_left2; auto.
    rewrite <- wand_sepcon_adjoint; sep_apply weak_exclusive_conflict; auto.
    rewrite FF_sepcon; auto.
  Qed.

  Program Definition acquire_spec :=
    TYPE (ProdType (ConstType _) InvType)
    WITH sh : _, h : _, R : _
    PRE [ tptr t_lock ]
       PROP (sh <> Share.bot)
       PARAMS (ptr_of h)
       SEP (lock_inv sh h R)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (lock_inv sh h R; R).
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
  Qed.

  Program Definition release_spec :=
    TYPE (ProdType (ProdType (ProdType (ConstType _) InvType) Mpred) Mpred)
    WITH sh : _, h : _, R : _, P : _, Q : _
    PRE [ tptr t_lock ]
       PROP (sh <> Share.bot)
       PARAMS (ptr_of h)
       SEP (weak_exclusive_mpred R && emp; |> lock_inv sh h R; P; lock_inv sh h R * P -* Q * R)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (Q).
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
    { setoid_rewrite later_nonexpansive; do 2 f_equal.
      apply lock_inv_super_non_expansive. }
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
    reflexivity.
  Qed.

  Program Definition release_spec_simple :=
    TYPE (ProdType (ConstType _) InvType)
    WITH sh : _, h : _, R : _
    PRE [ tptr t_lock ]
       PROP (sh <> Share.bot)
       PARAMS (ptr_of h)
       SEP (weak_exclusive_mpred R && emp; lock_inv sh h R; R)
    POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (lock_inv sh h R).
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as ((?, ?), ?); simpl.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; do 3 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    f_equal.
    { rewrite !approx_andp; f_equal.
      apply exclusive_mpred_super_non_expansive. }
    f_equal.
    apply lock_inv_super_non_expansive.
  Qed.
  Next Obligation.
  Proof.
    repeat intro.
    destruct x as ((?, ?), ?); simpl.
    unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 f_equal;
      rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
    apply lock_inv_super_non_expansive.
  Qed.

  Lemma release_simple : funspec_sub release_spec release_spec_simple.
  Proof.
    unfold funspec_sub; simpl.
    split; auto; intros ? ((sh, h), R) ?; Intros.
    eapply derives_trans, fupd_intro.
    Exists (nil : list Type) (sh, h, R, R, lock_inv sh h R) emp; entailer!.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; entailer!.
    apply wand_refl_cancel_right.
  Qed.

End lock_specs.

#[export] Hint Resolve lock_inv_isptr : saturate_local.
#[export] Hint Resolve lock_inv_exclusive data_at_exclusive data_at__exclusive field_at_exclusive field_at__exclusive : core.

Ltac lock_props := match goal with |-context[weak_exclusive_mpred ?P && emp] => sep_apply (exclusive_weak_exclusive P); [auto with share | try timeout 20 cancel] end.
