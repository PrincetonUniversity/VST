Require Import VST.veric.rmaps.
Require Import VST.veric.compcert_rmaps.
Require Import VST.progs.ghosts.
Require Import VST.progs.conclib.
Require Export VST.progs.invariants.
Require Export VST.progs.fupd.
Require Export atomics.general_atomics.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.

Set Bullet Behavior "Strict Subproofs".

(* Warning: it is UNSOUND to use both this file and acq_rel_atomics.v in the same proof! There is
   not yet an operational model that can validate the use of both SC and RA atomics. *)

Section SC_atomics.

Context {CS : compspecs}.

Definition AL_type := ProdType (ProdType (ProdType (ProdType (ConstType val)
  (ArrowType (ConstType iname) (ConstType Prop))) (ArrowType (ConstType iname) (ConstType Prop)))
  (ArrowType (ConstType Z) Mpred))
  (ConstType invG).

Program Definition load_SC_spec := TYPE AL_type
  WITH p : val, Eo : Ensemble iname, Ei : Ensemble iname, Q : Z -> mpred, inv_names : invG
  PRE [ 1%positive OF tptr tint ]
   PROP (Included Ei Eo)
   LOCAL (temp 1%positive p)
   SEP (|={Eo,Ei}=> EX sh : share, EX v : Z, !!(readable_share sh /\ repable_signed v) &&
              data_at sh tint (vint v) p * (data_at sh tint (vint v) p -* |={Ei,Eo}=> Q v))
  POST [ tint ]
   EX v : Z,
   PROP (repable_signed v)
   LOCAL (temp ret_temp (vint v))
   SEP (Q v).
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((?, ?), ?), ?), ?); simpl.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal;
    f_equal; rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem.
  setoid_rewrite fupd_nonexpansive; do 2 f_equal.
  rewrite !approx_exp; apply f_equal; extensionality sh.
  rewrite !approx_exp; apply f_equal; extensionality v. 
  rewrite !approx_sepcon; f_equal.
  setoid_rewrite fview_shift_nonexpansive; rewrite approx_idem; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((?, ?), ?), ?), ?); simpl.
  rewrite !approx_exp; apply f_equal; extensionality v.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
Qed.

Definition AS_type := ProdType (ProdType (ProdType (ProdType (ConstType (val * Z))
  (ArrowType (ConstType iname) (ConstType Prop))) (ArrowType (ConstType iname) (ConstType Prop)))
  Mpred) (ConstType invG).

Program Definition store_SC_spec := TYPE AS_type
  WITH p : val, v : Z, Eo : Ensemble iname, Ei : Ensemble iname, Q : mpred, inv_names : invG
  PRE [ 1%positive OF tptr tint, 2%positive OF tint ]
   PROP (repable_signed v)
   LOCAL (temp 1%positive p; temp 2%positive (vint v))
   SEP (|={Eo,Ei}=> EX sh : share, !!(writable_share sh) && data_at_ sh tint p *
      (data_at sh tint (vint v) p -* |={Ei,Eo}=> Q))
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (Q).
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((((?, ?), ?), ?), ?), ?); simpl.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal;
    f_equal; rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem.
  setoid_rewrite fupd_nonexpansive; do 2 f_equal.
  rewrite !approx_exp; apply f_equal; extensionality sh.
  rewrite !approx_sepcon; f_equal.
  setoid_rewrite fview_shift_nonexpansive; rewrite approx_idem; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((((?, ?), ?), ?), ?), ?); simpl.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
Qed.

Definition ACAS_type := ProdType (ProdType (ProdType (ProdType (ConstType (val * Z * Z))
  (ArrowType (ConstType iname) (ConstType Prop))) (ArrowType (ConstType iname) (ConstType Prop)))
  (ArrowType (ConstType Z) Mpred))
  (ConstType invG).

Program Definition CAS_SC_spec := TYPE ACAS_type
  WITH p : val, c : Z, v : Z, Eo : Ensemble iname, Ei : Ensemble iname, Q : Z -> mpred, inv_names : invG
  PRE [ 1%positive OF tptr tint, 2%positive OF tint, 3%positive OF tint ]
   PROP (repable_signed c; repable_signed v)
   LOCAL (temp 1%positive p; temp 2%positive (vint c); temp 3%positive (vint v))
   SEP (|={Eo,Ei}=> EX sh : share, EX v0 : Z, !!(writable_share sh /\ repable_signed v0) &&
              data_at sh tint (vint v0) p *
           (data_at sh tint (vint (if eq_dec v0 c then v else v0)) p -* |={Ei,Eo}=> Q v0))
  POST [ tint ]
   EX v' : Z,
   PROP (repable_signed v')
   LOCAL (temp ret_temp (vint (if eq_dec v' c then 1 else 0)))
   SEP (Q v').
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((((?, ?), ?), ?), ?), ?), ?); simpl.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal;
    f_equal; rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem.
  setoid_rewrite fupd_nonexpansive; do 2 f_equal.
  rewrite !approx_exp; apply f_equal; extensionality sh.
  rewrite !approx_exp; apply f_equal; extensionality v0.
  rewrite !approx_sepcon; f_equal.
  setoid_rewrite fview_shift_nonexpansive; rewrite approx_idem; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as ((((((?, ?), ?), ?), ?), ?), ?); simpl.
  rewrite !approx_exp; apply f_equal; extensionality vr.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
Qed.

Definition AEX_type := ProdType (ProdType (ProdType (ProdType (ConstType (val * Z))
  (ArrowType (ConstType iname) (ConstType Prop))) (ArrowType (ConstType iname) (ConstType Prop)))
  (ArrowType (ConstType Z) Mpred))
  (ConstType invG).

Program Definition AEX_SC_spec := TYPE AEX_type
  WITH p : val, v : Z, Eo : Ensemble iname, Ei : Ensemble iname, Q : Z -> mpred, inv_names : invG
  PRE [ 1%positive OF tptr tint, 2%positive OF tint ]
   PROP (repable_signed v)
   LOCAL (temp 1%positive p; temp 2%positive (vint v))
   SEP (|={Eo,Ei}=> EX sh : share, EX v0 : Z, !!(writable_share sh /\ repable_signed v0) &&
              data_at sh tint (vint v0) p *
        (data_at sh tint (vint v) p -* |={Ei,Eo}=> Q v0))
  POST [ tint ]
   EX v' : Z,
   PROP (repable_signed v')
   LOCAL (temp ret_temp (vint v'))
   SEP (Q v').
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((((?, ?), ?), ?), ?), ?); simpl.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal;
    f_equal; rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem.
  setoid_rewrite fupd_nonexpansive; do 2 f_equal.
  rewrite !approx_exp; apply f_equal; extensionality sh.
  rewrite !approx_exp; apply f_equal; extensionality v0.
  rewrite !approx_sepcon; f_equal.
  setoid_rewrite fview_shift_nonexpansive; rewrite approx_idem; auto.
Qed.
Next Obligation.
Proof.
  repeat intro.
  destruct x as (((((?, ?), ?), ?), ?), ?); simpl.
  rewrite !approx_exp; apply f_equal; extensionality vr.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; do 2 apply f_equal;
    rewrite !sepcon_emp, ?approx_sepcon, ?approx_idem; auto.
Qed.

End SC_atomics.
