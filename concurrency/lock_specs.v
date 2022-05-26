Require Import VST.veric.rmaps.
Require Import VST.concurrency.conclib.
Require Import VST.floyd.library.

(* lock invariants should be exclusive *)
Definition exclusive_mpred P := P * P |-- FF.

Program Definition weak_exclusive_mpred (P: mpred): mpred :=
  unfash (fash ((P * P) --> FF)).

Lemma corable_weak_exclusive R : seplog.corable (weak_exclusive_mpred R).
Proof.
  apply assert_lemmas.corable_unfash, _.
Qed.

Lemma exclusive_mpred_nonexpansive : nonexpansive weak_exclusive_mpred.
Proof.
  unfold weak_exclusive_mpred, nonexpansive; intros.
  apply @subtypes.eqp_unfash, @subtypes.eqp_subp_subp, eqp_refl.
  apply eqp_sepcon; apply predicates_hered.derives_refl.
Qed.

Lemma exclusive_mpred_super_non_expansive:
  forall R n, compcert_rmaps.RML.R.approx n (weak_exclusive_mpred R) =
    compcert_rmaps.RML.R.approx n (weak_exclusive_mpred (compcert_rmaps.RML.R.approx n R)).
Proof.
  apply nonexpansive_super_non_expansive, exclusive_mpred_nonexpansive.
Qed.

Lemma exclusive_weak_exclusive: forall R,
  exclusive_mpred R ->
  TT |-- weak_exclusive_mpred R.
Proof.
  intros; unfold weak_exclusive_mpred; unfold exclusive_mpred in H.
  unseal_derives; apply derives_unfash_fash; auto.
Qed.

Lemma weak_exclusive_conflict : forall P,
  (weak_exclusive_mpred P && emp) * P * P |-- FF.
Proof.
  intros.
  rewrite sepcon_assoc, <- andp_left_corable by (apply corable_weak_exclusive).
  unseal_derives; intros ? [].
  unfold weak_exclusive_mpred in H; specialize (H a ltac:(lia) _ _ (ageable.necR_refl _) (predicates_hered.ext_refl _)).
  apply H; auto.
Qed.

Lemma exclusive_sepcon1 : forall P Q (HP : exclusive_mpred P), exclusive_mpred (P * Q).
Proof.
  unfold exclusive_mpred; intros.
  eapply derives_trans, sepcon_FF_derives' with (P := Q * Q), HP; cancel; apply derives_refl.
Qed.

Lemma exclusive_sepcon2 : forall P Q (HP : exclusive_mpred Q), exclusive_mpred (P * Q).
Proof.
  intros; rewrite sepcon_comm; apply exclusive_sepcon1; auto.
Qed.

Lemma exclusive_andp1 : forall P Q (HP : exclusive_mpred P), exclusive_mpred (P && Q).
Proof.
  unfold exclusive_mpred; intros.
  eapply derives_trans, HP.
  apply sepcon_derives; apply andp_left1; auto.
Qed.

Lemma exclusive_andp2 : forall P Q (HQ : exclusive_mpred Q), exclusive_mpred (P && Q).
Proof.
  intros; rewrite andp_comm; apply exclusive_andp1; auto.
Qed.

Lemma exclusive_FF : exclusive_mpred FF.
Proof.
  unfold exclusive_mpred.
  rewrite FF_sepcon; auto.
Qed.

Lemma derives_exclusive : forall P Q (Hderives : P |-- Q) (HQ : exclusive_mpred Q),
  exclusive_mpred P.
Proof.
  unfold exclusive_mpred; intros.
  eapply derives_trans, HQ.
  apply sepcon_derives; auto.
Qed.

Lemma mapsto_exclusive : forall (sh : Share.t) (t : type) (v : val),
  sepalg.nonunit sh -> exclusive_mpred (EX v2 : _, mapsto sh t v v2).
Proof.
  intros; unfold exclusive_mpred.
  Intros v1 v2; apply mapsto_conflict; auto.
Qed.

Lemma field_at__exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) (fld : list gfield) (p : val),
  sepalg.nonidentity sh ->
  0 < sizeof (nested_field_type t fld) -> exclusive_mpred (field_at_ sh t fld p).
Proof.
  intros; apply field_at__conflict; auto.
Qed.

Lemma ex_field_at_exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) (fld : list gfield) (p : val),
  sepalg.nonidentity sh ->
  0 < sizeof (nested_field_type t fld) -> exclusive_mpred (EX v : _, field_at sh t fld v p).
Proof.
  intros; unfold exclusive_mpred.
  Intros v v'; apply field_at_conflict; auto.
Qed.

Corollary field_at_exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) (fld : list gfield) v (p : val),
  sepalg.nonidentity sh -> 0 < sizeof (nested_field_type t fld) -> exclusive_mpred (field_at sh t fld v p).
Proof.
  intros; eapply derives_exclusive, ex_field_at_exclusive; eauto.
  Exists v; apply derives_refl.
Qed.

Lemma ex_data_at_exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) (p : val),
  sepalg.nonidentity sh -> 0 < sizeof t -> exclusive_mpred (EX v : _, data_at sh t v p).
Proof.
  intros; unfold exclusive_mpred.
  Intros v v'; apply data_at_conflict; auto.
Qed.

Corollary data_at_exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) v (p : val),
  sepalg.nonidentity sh -> 0 < sizeof t -> exclusive_mpred (data_at sh t v p).
Proof.
  intros; eapply derives_exclusive, ex_data_at_exclusive; eauto.
  Exists v; apply derives_refl.
Qed.

Corollary data_at__exclusive : forall (cs : compspecs) (sh : Share.t) (t : type) (p : val),
  sepalg.nonidentity sh -> 0 < sizeof t -> exclusive_mpred (data_at_ sh t p).
Proof.
  intros; eapply derives_exclusive, data_at_exclusive; eauto.
  apply data_at__data_at; eauto.
Qed.

Class lock_impl := { t_lock : type; lock_handle : Type; ptr_of : lock_handle -> val;
  lock_inv : share -> lock_handle -> mpred -> mpred;
  lock_inv_nonexpansive : forall sh h, nonexpansive (lock_inv sh h);
  lock_inv_share_join : forall sh1 sh2 sh3 h R, sh1 <> Share.bot -> sh2 <> Share.bot ->
    sepalg.join sh1 sh2 sh3 -> lock_inv sh1 h R * lock_inv sh2 h R = lock_inv sh3 h R;
  lock_inv_exclusive : forall sh h R, exclusive_mpred (lock_inv sh h R);
  lock_inv_isptr : forall sh h R, lock_inv sh h R |-- !! isptr (ptr_of h) }.

Section lock_specs.

  Context {LI : lock_impl}.

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
     SEP (lock_inv Tsh h R; P; (P * R -* FF) && emp)
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

Ltac lock_props := rewrite ?sepcon_assoc; rewrite <- sepcon_emp at 1; rewrite sepcon_comm; apply sepcon_derives;
  [repeat apply andp_right; auto; eapply derives_trans;
   try (apply exclusive_weak_exclusive); auto with share exclusive |
   try timeout 20 cancel].
