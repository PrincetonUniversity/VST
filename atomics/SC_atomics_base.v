(* SC atomics without importing Iris *)

Require Import Ensembles.
Require Import VST.veric.rmaps.
Require Import VST.veric.compcert_rmaps.
Require Import VST.concurrency.ghosts.
Require Import VST.concurrency.conclib.
Require Import VST.floyd.library.
Require Import VST.zlist.sublist.

(* Warning: it is UNSOUND to use both this file and acq_rel_atomics.v in the same proof! There is
   not yet an operational model that can validate the use of both SC and RA atomics. *)

(* At present, due to complexities in the specifications of the C11 atomics (generics, _Atomic types, etc.), these are specs for wrapper functions for common cases.
   There's probably a more systematic approach possible. *)

Class atomic_int_impl := { atomic_int : type; atomic_int_at : share -> val -> val -> mpred;
  atomic_int_at__ : forall sh v p, atomic_int_at sh v p |-- atomic_int_at sh Vundef p;
  atomic_int_conflict : forall sh v v' p, sepalg.nonidentity sh -> atomic_int_at sh v p * atomic_int_at sh v' p |-- FF }.

Class atomic_ptr_impl := { atomic_ptr : type; atomic_ptr_at : share -> val -> val -> mpred;
  atomic_ptr_conflict : forall sh v v' p, sepalg.nonidentity sh -> atomic_ptr_at sh v p * atomic_ptr_at sh v' p |-- FF }.

Section SC_atomics.

Context {CS : compspecs} {AI : atomic_int_impl} {AP : atomic_ptr_impl}.

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

Definition AL_type := ProdType (ConstType (val * Ensemble nat * Ensemble nat)) (ArrowType (ConstType val) Mpred).

Program Definition atomic_load_spec := TYPE AL_type
  WITH p : val, Eo : Ensemble nat, Ei : Ensemble nat, Q : val -> mpred
  PRE [ tptr atomic_int ]
   PROP (Included Ei Eo)
   PARAMS (p)
   SEP (|={Eo,Ei}=> EX sh : share, EX v : val, !!(readable_share sh) &&
              atomic_int_at sh v p * (atomic_int_at sh v p -* |={Ei,Eo}=> Q v))
  POST [ tint ]
   EX v : val,
   PROP ()
   RETURN (v)
   SEP (Q v).
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((?, ?), ?), ?).
  unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; f_equal;
    f_equal; f_equal; rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  setoid_rewrite fupd_nonexpansive; do 2 f_equal.
  rewrite !approx_exp; apply f_equal; extensionality.
  rewrite !approx_exp; apply f_equal; extensionality.
  rewrite !approx_sepcon; f_equal.
  setoid_rewrite wand_nonexpansive_r; f_equal; f_equal.
  apply fupd_nonexpansive.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((?, ?), ?), ?); simpl.
  rewrite !approx_exp; apply f_equal; extensionality.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
Qed.

Definition AS_type := ProdType (ConstType (val * val * Ensemble nat * Ensemble nat)) Mpred.

Program Definition atomic_store_spec := TYPE AS_type
  WITH p : val, v : val, Eo : Ensemble nat, Ei : Ensemble nat, Q : mpred
  PRE [ tptr atomic_int, tint ]
   PROP (Included Ei Eo)
   PARAMS (p; v)
   SEP (|={Eo,Ei}=> EX sh : share, !!(writable_share sh) && atomic_int_at sh Vundef p *
      (atomic_int_at sh v p -* |={Ei,Eo}=> Q))
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (Q).
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((?, ?), ?), ?), ?).
  unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; f_equal;
    f_equal; f_equal; rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  setoid_rewrite fupd_nonexpansive; do 2 f_equal.
  rewrite !approx_exp; apply f_equal; extensionality sh.
  rewrite !approx_sepcon; f_equal.
  setoid_rewrite wand_nonexpansive_r; f_equal; f_equal.
  apply fupd_nonexpansive.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((?, ?), ?), ?), ?); simpl.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
Qed.

Definition ACAS_type := ProdType (ProdType (ProdType (ConstType (val * share * val * val * val))
  (ConstType (Ensemble nat))) (ConstType (Ensemble nat)))
  (ArrowType (ConstType val) Mpred).

Program Definition atomic_CAS_spec := TYPE ACAS_type
  WITH p : val, shc : share, pc : val, c : val, v : val, Eo : Ensemble nat, Ei : Ensemble nat, Q : val -> mpred
  PRE [ tptr atomic_int, tptr tint, tint ]
   PROP (readable_share shc; Included Ei Eo)
   PARAMS (p; pc; v)
   SEP (data_at shc tint c pc; |={Eo,Ei}=> EX sh : share, EX v0 : val,
      !!(writable_share sh) && atomic_int_at sh v0 p *
           (atomic_int_at sh (if eq_dec v0 c then v else v0) p -* |={Ei,Eo}=> Q v0))
  POST [ tint ]
   EX v' : val,
   PROP ()
   LOCAL (temp ret_temp (vint (if eq_dec v' c then 1 else 0)))
   SEP (data_at shc tint v' pc; Q v').
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((((((?, ?), ?), ?), ?), ?), ?), ?).
  unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; f_equal;
    f_equal; f_equal; rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  f_equal.
  setoid_rewrite fupd_nonexpansive; do 2 f_equal.
  rewrite !approx_exp; apply f_equal; extensionality sh.
  rewrite !approx_exp; apply f_equal; extensionality.
  rewrite !approx_sepcon; f_equal.
  setoid_rewrite wand_nonexpansive_r; f_equal; f_equal.
  apply fupd_nonexpansive.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((((((?, ?), ?), ?), ?), ?), ?), ?); simpl.
  rewrite !approx_exp; apply f_equal; extensionality vr.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
Qed.

Definition AEX_type := ProdType (ProdType (ProdType (ConstType (val * val))
  (ConstType (Ensemble nat))) (ConstType (Ensemble nat)))
  (ArrowType (ConstType val) Mpred).

Program Definition atomic_exchange_spec := TYPE AEX_type
  WITH p : val, v : val, Eo : Ensemble nat, Ei : Ensemble nat, Q : val -> mpred
  PRE [ tptr tint, tint ]
   PROP (Included Ei Eo)
   PARAMS (p; v)
   SEP (|={Eo,Ei}=> EX sh : share, EX v0 : val, !!(writable_share sh) &&
              data_at sh tint v0 p *
        (data_at sh tint v p -* |={Ei,Eo}=> Q v0))
  POST [ tint ]
   EX v' : val,
   PROP ()
   LOCAL (temp ret_temp v')
   SEP (Q v').
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((?, ?), ?), ?), ?).
  unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; f_equal;
    f_equal; f_equal; rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  setoid_rewrite fupd_nonexpansive; do 2 f_equal.
  rewrite !approx_exp; apply f_equal; extensionality sh.
  rewrite !approx_exp; apply f_equal; extensionality.
  rewrite !approx_sepcon; f_equal.
  setoid_rewrite wand_nonexpansive_r; f_equal; f_equal.
  apply fupd_nonexpansive.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((?, ?), ?), ?), ?); simpl.
  rewrite !approx_exp; apply f_equal; extensionality vr.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
Qed.

(* specs for pointer operations *)

Definition ALI_ptr_type := ProdType (ProdType (ProdType (ConstType val)
  (ConstType (Ensemble nat))) (ConstType (Ensemble nat)))
  (ArrowType (ConstType val) Mpred).

Program Definition atomic_load_ptr_spec := TYPE ALI_ptr_type
  WITH p : val, Eo : (Ensemble nat), Ei : (Ensemble nat), Q : val -> mpred
  PRE [ tptr atomic_ptr ]
   PROP (Included Ei Eo)
   PARAMS (p)
   SEP (|={Eo,Ei}=> EX sh : share, EX v : val, !!(readable_share sh) &&
              atomic_ptr_at sh v p * (atomic_ptr_at sh v p -* |={Ei,Eo}=> Q v))
  POST [ tptr Tvoid ]
   EX v : val,
   PROP ()
   LOCAL (temp ret_temp v)
   SEP (Q v).
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((?, ?), ?), ?); simpl.
  unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; f_equal;
    f_equal; f_equal; rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  setoid_rewrite fupd_nonexpansive; do 2 f_equal.
  rewrite !approx_exp; apply f_equal; extensionality sh.
  rewrite !approx_exp; apply f_equal; extensionality v.
  rewrite !approx_sepcon; f_equal.
  setoid_rewrite ghosts.wand_nonexpansive_r; do 2 f_equal.
  apply fupd_nonexpansive.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((?, ?), ?), ?); simpl.
  rewrite !approx_exp; apply f_equal; extensionality v.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
Qed.


Definition ASI_ptr_type := ProdType (ProdType (ProdType (ConstType (val * val))
  (ConstType (Ensemble nat))) (ConstType (Ensemble nat))) Mpred.

Program Definition atomic_store_ptr_spec := TYPE ASI_ptr_type
  WITH p : val, v : val, Eo : (Ensemble nat), Ei : (Ensemble nat), Q : mpred
  PRE [ tptr atomic_ptr, tptr Tvoid ]
   PROP (Included Ei Eo)
   PARAMS (p; v)
   SEP (|={Eo,Ei}=> EX sh : share, !!(writable_share sh) && atomic_ptr_at sh Vundef p *
      (atomic_ptr_at sh v p -* |={Ei,Eo}=> Q))
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (Q).
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((?, ?), ?), ?), ?); simpl.
  unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; f_equal;
    f_equal; f_equal; rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  setoid_rewrite fupd_nonexpansive; do 2 f_equal.
  rewrite !approx_exp; apply f_equal; extensionality sh.
  rewrite !approx_sepcon; f_equal.
  setoid_rewrite ghosts.wand_nonexpansive_r; do 2 f_equal.
  apply fupd_nonexpansive.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((?, ?), ?), ?), ?); simpl.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
Qed.


Definition ACASI_ptr_type := ProdType (ProdType (ProdType (ConstType (val * share * val * val * val))
  (ConstType (Ensemble nat))) (ConstType (Ensemble nat)))
  (ArrowType (ConstType val) Mpred).

Program Definition atomic_CAS_ptr_spec := TYPE ACASI_ptr_type
  WITH p : val, shc : share, pc : val, c : val, v : val, Eo : (Ensemble nat), Ei : (Ensemble nat), Q : val -> mpred
  PRE [ tptr atomic_ptr, tptr (tptr Tvoid), tptr Tvoid ]
   PROP (readable_share shc; Included Ei Eo)
   PARAMS (p; pc; v)
   SEP (data_at shc (tptr Tvoid) c pc; |={Eo,Ei}=> EX sh : share, EX v0 : val,
      !!(writable_share sh ) && atomic_ptr_at sh v0 p *
           (atomic_ptr_at sh (if eq_dec v0 c then v else v0) p -* |={Ei,Eo}=> Q v0))
  POST [ tint ]
   EX v' : val,
   PROP ()
   LOCAL (temp ret_temp (vint (if eq_dec v' c then 1 else 0)))
   SEP (data_at shc (tptr Tvoid) c pc; Q v').
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((((((?, ?), ?), ?), ?), ?), ?), ?); simpl.
  unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; f_equal;
    f_equal; f_equal; rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  setoid_rewrite fupd_nonexpansive; do 3 f_equal.
  rewrite !approx_exp; apply f_equal; extensionality sh.
  rewrite !approx_exp; apply f_equal; extensionality v'.
  rewrite !approx_sepcon; f_equal.
  setoid_rewrite ghosts.wand_nonexpansive_r; do 2 f_equal.
  apply fupd_nonexpansive.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((((((?, ?), ?), ?), ?), ?), ?), ?); simpl.
  rewrite !approx_exp; apply f_equal; extensionality vr.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
Qed.


Definition AEXI_ptr_type := ProdType (ProdType (ProdType (ConstType (val * val))
  (ConstType (Ensemble nat))) (ConstType (Ensemble nat)))
  (ArrowType (ConstType val) Mpred).

Program Definition atomic_exchange_ptr_spec := TYPE AEXI_ptr_type
  WITH p : val, v : val, Eo : (Ensemble nat), Ei : (Ensemble nat), Q : val -> mpred
  PRE [ tptr atomic_ptr, tptr Tvoid ]
   PROP (Included Ei Eo)
   PARAMS (p; v)
   SEP (|={Eo,Ei}=> EX sh : share, EX v0 : val, !!(writable_share sh ) &&
              atomic_ptr_at sh v0 p *
        (atomic_ptr_at sh v p -* |={Ei,Eo}=> Q v0))
  POST [ tint ]
   EX v' : val,
   PROP ()
   LOCAL (temp ret_temp v')
   SEP (Q v').
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((?, ?), ?), ?), ?); simpl.
  unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl; rewrite !approx_andp; f_equal;
    f_equal; f_equal; rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  setoid_rewrite fupd_nonexpansive; do 2 f_equal.
  rewrite !approx_exp; apply f_equal; extensionality sh.
  rewrite !approx_exp; apply f_equal; extensionality v'.
  rewrite !approx_sepcon; f_equal.
  setoid_rewrite ghosts.wand_nonexpansive_r; do 2 f_equal.
  apply fupd_nonexpansive.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((?, ?), ?), ?), ?); simpl.
  rewrite !approx_exp; apply f_equal; extensionality vr.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
Qed.

End SC_atomics.
