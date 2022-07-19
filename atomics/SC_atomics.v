Require Import stdpp.coPset.
Require Import VST.veric.rmaps.
Require Import VST.veric.compcert_rmaps.
Require Import VST.concurrency.ghosts.
Require Import VST.concurrency.conclib.
Require Import VST.concurrency.fupd.
Require Export VST.atomics.general_atomics.
Require Import VST.atomics.SC_atomics_base.
Require Import VST.floyd.library.
Require Import VST.zlist.sublist.

(* Warning: it is UNSOUND to use both this file and acq_rel_atomics.v in the same proof! There is
   not yet an operational model that can validate the use of both SC and RA atomics. *)

(* At present, due to complexities in the specifications of the C11 atomics (generics, _Atomic types, etc.), these are specs for wrapper functions for common cases. *)

Section SC_atomics.

Context {CS : compspecs}  {AI : atomic_int_impl} {AP : atomic_ptr_impl}.

Definition make_atomic_spec :=
  WITH v : val
  PRE [ tint ]
    PROP ()
    PARAMS (v)
    SEP ()
  POST [ tptr atomic_int ]
   EX p : val,
    PROP ()
    RETURN (p)
    SEP (atomic_int_at Ews v p).

Definition make_atomic_ptr_spec :=
  WITH v : val
  PRE [ tptr Tvoid ]
    PROP ()
    PARAMS (v)
    SEP ()
  POST [ tptr atomic_ptr ]
   EX p : val,
    PROP (is_pointer_or_null p)
    RETURN (p)
    SEP (atomic_ptr_at Ews v p).

Definition free_atomic_ptr_spec :=
  WITH p : val
  PRE [ tptr atomic_ptr ]
    PROP (is_pointer_or_null p)
    PARAMS (p)
    SEP (EX v : val, atomic_ptr_at Ews v p)
  POST[ tvoid ]
    PROP ()
    LOCAL ()
    SEP ().

Definition free_atomic_int_spec :=
  WITH p : val
  PRE [ tptr atomic_int ]
    PROP (is_pointer_or_null p)
    PARAMS (p)
    SEP (EX v : val, atomic_int_at Ews v p)
  POST[ tvoid ]
    PROP ()
    LOCAL ()
    SEP ().

Definition AL_type := ProdType (ProdType (ProdType (ConstType val)
  (ConstType coPset)) (ConstType coPset))
  (ArrowType (ConstType val) Mpred).

Program Definition atomic_load_spec := TYPE AL_type
  WITH p : val, Eo : coPset, Ei : coPset, Q : val -> mpred
  PRE [ tptr atomic_int ]
   PROP (subseteq Ei Eo)
   PARAMS (p)
   SEP (|={Eo,Ei}=> EX sh : share, EX v : val, !!(readable_share sh) &&
              atomic_int_at sh v p * (atomic_int_at sh v p -* |={Ei,Eo}=> Q v))%I
  POST [ tint ]
   EX v : val,
   PROP ()
   RETURN (v)
   SEP (Q v).
Next Obligation.
Proof.
  repeat intro.
  unfold PROPx, PARAMSx, SEPx; simpl; rewrite !approx_andp; f_equal;
    f_equal; rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  setoid_rewrite fupd_nonexpansive; do 3 f_equal.
  rewrite !approx_exp; apply f_equal; extensionality sh.
  rewrite !approx_exp; apply f_equal; extensionality v.
  rewrite !approx_sepcon; f_equal.
  setoid_rewrite fview_shift_nonexpansive; rewrite approx_idem; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  rewrite !approx_exp; apply f_equal; extensionality v.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
Qed.

Definition AS_type := ProdType (ProdType (ProdType (ConstType (val * val))
  (ConstType coPset)) (ConstType coPset)) Mpred.

Program Definition atomic_store_spec := TYPE AS_type
  WITH p : val, v : val, Eo : coPset, Ei : coPset, Q : mpred
  PRE [ tptr atomic_int, tint ]
   PROP (subseteq Ei Eo)
   PARAMS (p; v)
   SEP (|={Eo,Ei}=> EX sh : share, !!(writable_share sh) && atomic_int_at sh Vundef p *
      (atomic_int_at sh v p -* |={Ei,Eo}=> Q))%I
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (Q).
Next Obligation.
Proof.
  repeat intro.
  unfold PROPx, PARAMSx, SEPx; simpl; rewrite !approx_andp; f_equal;
    f_equal; rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  setoid_rewrite fupd_nonexpansive; do 3 f_equal.
  rewrite !approx_exp; apply f_equal; extensionality sh.
  rewrite !approx_sepcon; f_equal.
  setoid_rewrite fview_shift_nonexpansive; rewrite approx_idem; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
Qed.

Definition ACAS_type := ProdType (ProdType (ProdType (ConstType (val * share * val * val * val))
  (ConstType coPset)) (ConstType coPset))
  (ArrowType (ConstType val) Mpred).

Program Definition atomic_CAS_spec := TYPE ACAS_type
  WITH p : val, shc : share, pc : val, c : val, v : val, Eo : coPset, Ei : coPset, Q : val -> mpred
  PRE [ tptr atomic_int, tptr tint, tint ]
   PROP (readable_share shc; subseteq Ei Eo)
   PARAMS (p; pc; v)
   SEP (data_at shc tint c pc; |={Eo,Ei}=> EX sh : share, EX v0 : val,
      !!(writable_share sh) && atomic_int_at sh v0 p *
           (atomic_int_at sh (if eq_dec v0 c then v else v0) p -* |={Ei,Eo}=> Q v0))%I
  POST [ tint ]
   EX v' : val,
   PROP ()
   LOCAL (temp ret_temp (vint (if eq_dec v' c then 1 else 0)))
   SEP (data_at shc tint v' pc; Q v').
Next Obligation.
Proof.
  repeat intro.
  unfold PROPx, PARAMSx, SEPx; simpl; rewrite !approx_andp; f_equal;
    f_equal; rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  unfold argsassert2assert; rewrite !approx_sepcon; do 2 f_equal.
  setoid_rewrite fupd_nonexpansive; do 2 f_equal.
  rewrite !approx_exp; apply f_equal; extensionality sh.
  rewrite !approx_exp; apply f_equal; extensionality v2.
  rewrite !approx_sepcon; f_equal.
  setoid_rewrite fview_shift_nonexpansive; rewrite approx_idem; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  rewrite !approx_exp; apply f_equal; extensionality vr.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
Qed.

Definition AEX_type := ProdType (ProdType (ProdType (ConstType (val * val))
  (ConstType coPset)) (ConstType coPset))
  (ArrowType (ConstType val) Mpred).

Program Definition atomic_exchange_spec := TYPE AEX_type
  WITH p : val, v : val, Eo : coPset, Ei : coPset, Q : val -> mpred
  PRE [ tptr tint, tint ]
   PROP (subseteq Ei Eo)
   PARAMS (p; v)
   SEP (|={Eo,Ei}=> EX sh : share, EX v0 : val, !!(writable_share sh) &&
              data_at sh tint v0 p *
        (data_at sh tint v p -* |={Ei,Eo}=> Q v0))%I
  POST [ tint ]
   EX v' : val,
   PROP ()
   LOCAL (temp ret_temp v')
   SEP (Q v').
Next Obligation.
Proof.
  repeat intro.
  unfold PROPx, PARAMSx, SEPx; simpl; rewrite !approx_andp; f_equal;
    f_equal; rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  unfold argsassert2assert; f_equal.
  setoid_rewrite fupd_nonexpansive; do 2 f_equal.
  rewrite !approx_exp; apply f_equal; extensionality sh.
  rewrite !approx_exp; apply f_equal; extensionality v0.
  rewrite !approx_sepcon; f_equal.
  setoid_rewrite fview_shift_nonexpansive; rewrite approx_idem; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  rewrite !approx_exp; apply f_equal; extensionality vr.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
Qed.

(* subspecs for integer operations *)
Definition ALI_type := ProdType (ProdType (ProdType (ConstType val)
  (ConstType coPset)) (ConstType coPset))
  (ArrowType (ConstType Z) Mpred).

Program Definition atomic_load_int_spec := TYPE ALI_type
  WITH p : val, Eo : coPset, Ei : coPset, Q : Z -> mpred
  PRE [ tptr atomic_int ]
   PROP (subseteq Ei Eo)
   PARAMS (p)
   SEP (|={Eo,Ei}=> EX sh : share, EX v : Z, !!(readable_share sh /\ repable_signed v) &&
              atomic_int_at sh (vint v) p * (atomic_int_at sh (vint v) p -* |={Ei,Eo}=> Q v))%I
  POST [ tint ]
   EX v : Z,
   PROP (repable_signed v)
   LOCAL (temp ret_temp (vint v))
   SEP (Q v).
Next Obligation.
Proof.
  repeat intro.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal;
    f_equal; rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  setoid_rewrite fupd_nonexpansive; do 3 f_equal.
  rewrite !approx_exp; apply f_equal; extensionality sh.
  rewrite !approx_exp; apply f_equal; extensionality v.
  rewrite !approx_sepcon; f_equal.
  setoid_rewrite fview_shift_nonexpansive; rewrite approx_idem; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  rewrite !approx_exp; apply f_equal; extensionality v.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
Qed.

Lemma atomic_load_int : funspec_sub atomic_load_spec atomic_load_int_spec.
Proof.
  apply prove_funspec_sub.
  split; auto; intros; simpl in *.
  destruct x2 as (((p, Eo), Ei), Q).
  intros; iIntros "[_ H] !>".
  iExists nil, (p, Eo, Ei, fun v => match v with Vint i => Q (Int.signed i) | _ => FF end), emp.
  rewrite emp_sepcon; iSplit.
  - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl.
    iDestruct "H" as "($ & $ & $ & H & $)".
    iMod "H"; iModIntro.
    iDestruct "H" as (sh v) "[[% H1] H2]".
    destruct H.
    iExists sh, (vint v); iFrame.
    rewrite Int.signed_repr; auto.
  - iPureIntro.
    iIntros (?) "(_ & _ & H)".
    unfold PROPx, LOCALx, SEPx; simpl.
    iDestruct "H" as (r) "(_ & % & Q & _)".
    destruct H, r; try done.
    iExists (Int.signed i); iSplit; auto.
    { iPureIntro; split; auto.
      apply Int.signed_range. }
    iSplit; [iSplit; auto|].
    { rewrite Int.repr_signed; auto. }
    rewrite sepcon_emp; auto.
Qed.

Definition ASI_type := ProdType (ProdType (ProdType (ConstType (val * Z))
  (ConstType coPset)) (ConstType coPset)) Mpred.

Program Definition atomic_store_int_spec := TYPE ASI_type
  WITH p : val, v : Z, Eo : coPset, Ei : coPset, Q : mpred
  PRE [ tptr atomic_int, tint ]
   PROP (repable_signed v; subseteq Ei Eo)
   PARAMS (p; vint v)
   SEP (|={Eo,Ei}=> EX sh : share, !!(writable_share sh) && atomic_int_at sh Vundef p *
      (atomic_int_at sh (vint v) p -* |={Ei,Eo}=> Q))%I
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (Q).
Next Obligation.
Proof.
  repeat intro.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal;
    f_equal; rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  setoid_rewrite fupd_nonexpansive; do 3 f_equal.
  rewrite !approx_exp; apply f_equal; extensionality sh.
  rewrite !approx_sepcon; f_equal.
  setoid_rewrite fview_shift_nonexpansive; rewrite approx_idem; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
Qed.

Lemma atomic_store_int : funspec_sub atomic_store_spec atomic_store_int_spec.
Proof.
  apply prove_funspec_sub.
  split; auto; intros; simpl in *.
  destruct x2 as ((((p, v), Eo), Ei), Q).
  intros; iIntros "[_ H] !>".
  iExists nil, (p, vint v, Eo, Ei, Q), emp.
  rewrite emp_sepcon; iSplit.
  - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx; simpl.
    iDestruct "H" as "(% & $ & $ & H & $)".
    destruct H; auto.
  - iPureIntro.
    by iIntros (?) "(_ & _ & $)".
Qed.

Definition ACASI_type := ProdType (ProdType (ProdType (ConstType (val * share * val * Z * Z))
  (ConstType coPset)) (ConstType coPset))
  (ArrowType (ConstType Z) Mpred).

Program Definition atomic_CAS_int_spec := TYPE ACASI_type
  WITH p : val, shc : share, pc : val, c : Z, v : Z, Eo : coPset, Ei : coPset, Q : Z -> mpred
  PRE [ tptr atomic_int, tptr tint, tint ]
   PROP (repable_signed c; repable_signed v; readable_share shc; subseteq Ei Eo)
   PARAMS (p; pc; vint v)
   SEP (data_at shc tint (vint c) pc; |={Eo,Ei}=> EX sh : share, EX v0 : Z,
      !!(writable_share sh /\ repable_signed v0) && atomic_int_at sh (vint v0) p *
           (atomic_int_at sh (vint (if eq_dec v0 c then v else v0)) p -* |={Ei,Eo}=> Q v0))%I
  POST [ tint ]
   EX v' : Z,
   PROP (repable_signed v')
   LOCAL (temp ret_temp (vint (if eq_dec v' c then 1 else 0)))
   SEP (data_at shc tint (vint v') pc; Q v').
Next Obligation.
Proof.
  repeat intro.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal;
    f_equal; rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  unfold argsassert2assert; rewrite !approx_sepcon; do 2 f_equal.
  setoid_rewrite fupd_nonexpansive; do 2 f_equal.
  rewrite !approx_exp; apply f_equal; extensionality sh.
  rewrite !approx_exp; apply f_equal; extensionality v2.
  rewrite !approx_sepcon; f_equal.
  setoid_rewrite fview_shift_nonexpansive; rewrite approx_idem; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  rewrite !approx_exp; apply f_equal; extensionality vr.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
Qed.

Lemma atomic_CAS_int : funspec_sub atomic_CAS_spec atomic_CAS_int_spec.
Proof.
  apply prove_funspec_sub.
  split; auto; intros; simpl in *.
  destruct x2 as (((((((p, shc), pc), c), v), Eo), Ei), Q).
  intros; iIntros "[_ H] !>".
  iExists nil, (p, shc, pc, vint c, vint v, Eo, Ei, fun v => match v with Vint i => Q (Int.signed i) | _ => FF end), emp.
  rewrite emp_sepcon; iSplit.
  - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx; simpl.
    iDestruct "H" as "(% & $ & $ & $ & H & $)".
    destruct H as (? & ? & ?); iSplit; auto.
    iMod "H"; iModIntro.
    iDestruct "H" as (sh v0) "[[% H1] H2]".
    destruct H2.
    iExists sh, (vint v0); iFrame.
    rewrite -> Int.signed_repr by auto.
    iSplit; first done.
    if_tac.
    + subst; rewrite eq_dec_refl; done.
    + if_tac; last done.
      match goal with H : vint _ = vint _ |- _ => apply Vint_inj, repr_inj_signed in H end; auto; contradiction.
  - unfold PROPx, LOCALx, SEPx; simpl.
    iDestruct "H" as "[% _]".
    destruct H as [Hc _].
    iPureIntro.
    iIntros (?) "(_ & _ & H)".
    iDestruct "H" as (r) "(_ & % & ? & Q & _)".
    destruct H, r; try done.
    iExists (Int.signed i); iSplit; auto.
    { iPureIntro; split; auto.
      apply Int.signed_range. }
    iSplit; [iSplit; auto|].
    { if_tac; if_tac in H; auto; subst.
      + rewrite Int.repr_signed in H2; contradiction.
      + apply Vint_inj in H2; subst.
        rewrite -> Int.signed_repr in H1 by auto; contradiction. }
    rewrite Int.repr_signed sepcon_emp; iFrame.
Qed.

Definition AEXI_type := ProdType (ProdType (ProdType (ConstType (val * Z))
  (ConstType coPset)) (ConstType coPset))
  (ArrowType (ConstType Z) Mpred).

Program Definition atomic_exchange_int_spec := TYPE AEXI_type
  WITH p : val, v : Z, Eo : coPset, Ei : coPset, Q : Z -> mpred
  PRE [ tptr tint, tint ]
   PROP (repable_signed v; subseteq Ei Eo)
   PARAMS (p; vint v)
   SEP (|={Eo,Ei}=> EX sh : share, EX v0 : Z, !!(writable_share sh /\ repable_signed v0) &&
              data_at sh tint (vint v0) p *
        (data_at sh tint (vint v) p -* |={Ei,Eo}=> Q v0))%I
  POST [ tint ]
   EX v' : Z,
   PROP (repable_signed v')
   LOCAL (temp ret_temp (vint v'))
   SEP (Q v').
Next Obligation.
Proof.
  repeat intro.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal;
    f_equal; rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  setoid_rewrite fupd_nonexpansive; do 3 f_equal.
  rewrite !approx_exp; apply f_equal; extensionality sh.
  rewrite !approx_exp; apply f_equal; extensionality v0.
  rewrite !approx_sepcon; f_equal.
  setoid_rewrite fview_shift_nonexpansive; rewrite approx_idem; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  rewrite !approx_exp; apply f_equal; extensionality vr.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
Qed.

Lemma atomic_exchange_int : funspec_sub atomic_exchange_spec atomic_exchange_int_spec.
Proof.
  apply prove_funspec_sub.
  split; auto; intros; simpl in *.
  destruct x2 as ((((p, v), Eo), Ei), Q).
  intros; iIntros "[_ H] !>".
  iExists nil, (p, vint v, Eo, Ei, fun v => match v with Vint i => Q (Int.signed i) | _ => FF end), emp.
  rewrite emp_sepcon; iSplit.
  - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx; simpl.
    iDestruct "H" as "(% & $ & $ & H & $)".
    destruct H; iSplit; auto.
    iMod "H"; iModIntro.
    iDestruct "H" as (sh v0) "[[% H1] H2]".
    destruct H1.
    iExists sh, (vint v0); iFrame.
    rewrite -> Int.signed_repr; auto.
  - unfold PROPx, LOCALx, SEPx; simpl.
    iPureIntro.
    iIntros (?) "(_ & _ & H)".
    iDestruct "H" as (r) "(_ & % & Q & _)".
    destruct H, r; try done.
    iExists (Int.signed i); iSplit; auto.
    { iPureIntro; split; auto.
      apply Int.signed_range. }
    iSplit; [iSplit; auto|].
    { rewrite Int.repr_signed; auto. }
    rewrite sepcon_emp; iFrame.
Qed.

(* specs for pointer operations *)

Definition ALI_ptr_type := ProdType (ProdType (ProdType (ConstType val)
  (ConstType coPset)) (ConstType coPset))
  (ArrowType (ConstType val) Mpred).

Program Definition atomic_load_ptr_spec := TYPE ALI_ptr_type
  WITH p : val, Eo : coPset, Ei : coPset, Q : val -> mpred
  PRE [ tptr atomic_ptr ]
   PROP (subseteq Ei Eo)
   PARAMS (p)
   SEP (|={Eo,Ei}=> EX sh : share, EX v : val, !!(readable_share sh ) &&
              atomic_ptr_at sh v p * (atomic_ptr_at sh v p -* |={Ei,Eo}=> Q v))%I
  POST [ tptr Tvoid ]
   EX v : val,
   PROP ()
   LOCAL (temp ret_temp v)
   SEP (Q v).
Next Obligation.
Proof.
  repeat intro.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal;
    f_equal; rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  setoid_rewrite fupd_nonexpansive; do 3 f_equal.
  rewrite !approx_exp; apply f_equal; extensionality sh.
  rewrite !approx_exp; apply f_equal; extensionality v.
  rewrite !approx_sepcon; f_equal.
  setoid_rewrite fview_shift_nonexpansive; rewrite approx_idem; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  rewrite !approx_exp; apply f_equal; extensionality v.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
Qed.


Definition ASI_ptr_type := ProdType (ProdType (ProdType (ConstType (val * val))
  (ConstType coPset)) (ConstType coPset)) Mpred.

Program Definition atomic_store_ptr_spec := TYPE ASI_ptr_type
  WITH p : val, v : val, Eo : coPset, Ei : coPset, Q : mpred
  PRE [ tptr atomic_ptr, tptr Tvoid ]
   PROP (subseteq Ei Eo)
   PARAMS (p; v)
   SEP (|={Eo,Ei}=> EX sh : share, !!(writable_share sh) && atomic_ptr_at sh Vundef p *
      (atomic_ptr_at sh v p -* |={Ei,Eo}=> Q))%I
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (Q).
Next Obligation.
Proof.
  repeat intro.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal;
    f_equal; rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  setoid_rewrite fupd_nonexpansive; do 3 f_equal.
  rewrite !approx_exp; apply f_equal; extensionality sh.
  rewrite !approx_sepcon; f_equal.
  setoid_rewrite fview_shift_nonexpansive; rewrite approx_idem; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
Qed.


Definition ACASI_ptr_type := ProdType (ProdType (ProdType (ConstType (val * share * val * val * val))
  (ConstType coPset)) (ConstType coPset))
  (ArrowType (ConstType val) Mpred).

Program Definition atomic_CAS_ptr_spec := TYPE ACASI_ptr_type
  WITH p : val, shc : share, pc : val, c : val, v : val, Eo : coPset, Ei : coPset, Q : val -> mpred
  PRE [ tptr atomic_ptr, tptr (tptr Tvoid), tptr Tvoid ]
   PROP (readable_share shc; subseteq Ei Eo)
   PARAMS (p; pc; v)
   SEP (data_at shc (tptr Tvoid) c pc; |={Eo,Ei}=> EX sh : share, EX v0 : val,
      !!(writable_share sh ) && atomic_ptr_at sh v0 p *
           (atomic_ptr_at sh (if eq_dec v0 c then v else v0) p -* |={Ei,Eo}=> Q v0))%I
  POST [ tint ]
   EX v' : val,
   PROP ()
   LOCAL (temp ret_temp (vint (if eq_dec v' c then 1 else 0)))
   SEP (data_at shc (tptr Tvoid) c pc; Q v').
Next Obligation.
Proof.
  repeat intro.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal;
    f_equal; rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  unfold argsassert2assert; rewrite !approx_sepcon; f_equal.
  setoid_rewrite fupd_nonexpansive; do 3 f_equal.
  rewrite !approx_exp; apply f_equal; extensionality sh.
  rewrite !approx_exp; apply f_equal; extensionality v2.
  rewrite !approx_sepcon; f_equal.
  setoid_rewrite fview_shift_nonexpansive; rewrite approx_idem; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  rewrite !approx_exp; apply f_equal; extensionality vr.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
Qed.


Definition AEXI_ptr_type := ProdType (ProdType (ProdType (ConstType (val * val))
  (ConstType coPset)) (ConstType coPset))
  (ArrowType (ConstType val) Mpred).

Program Definition atomic_exchange_ptr_spec := TYPE AEXI_ptr_type
  WITH p : val, v : val, Eo : coPset, Ei : coPset, Q : val -> mpred
  PRE [ tptr atomic_ptr, tptr Tvoid ]
   PROP (subseteq Ei Eo)
   PARAMS (p; v)
   SEP (|={Eo,Ei}=> EX sh : share, EX v0 : val, !!(writable_share sh ) &&
              atomic_ptr_at sh v0 p *
        (atomic_ptr_at sh v p -* |={Ei,Eo}=> Q v0))%I
  POST [ tint ]
   EX v' : val,
   PROP ()
   LOCAL (temp ret_temp v')
   SEP (Q v').
Next Obligation.
Proof.
  repeat intro.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal;
    f_equal; rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  setoid_rewrite fupd_nonexpansive; do 3 f_equal.
  rewrite !approx_exp; apply f_equal; extensionality sh.
  rewrite !approx_exp; apply f_equal; extensionality v0.
  rewrite !approx_sepcon; f_equal.
  setoid_rewrite fview_shift_nonexpansive; rewrite approx_idem; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  rewrite !approx_exp; apply f_equal; extensionality vr.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
Qed.

End SC_atomics.
