Require Import VST.veric.rmaps.
Require Import VST.veric.compcert_rmaps.
Require Import VST.progs.ghosts.
Require Import VST.progs.conclib.
Require Export VST.progs.invariants.
Require Export VST.progs.fupd.
Require Export VST.atomics.general_atomics.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.

Set Bullet Behavior "Strict Subproofs".

(* Warning: it is UNSOUND to use both this file and acq_rel_atomics.v in the same proof! There is
   not yet an operational model that can validate the use of both SC and RA atomics. *)

(* At present, due to complexities in the specifications of the C11 atomics (generics, _Atomic types, etc.), these are specs for wrapper functions for common cases. *)

Section SC_atomics.

Context {CS : compspecs}.
(*Definition atom_int := Tint I32 Signed {| attr_volatile := false; attr_alignas := Some 32%N |}.*)
(* Is this what _Atomic int actually should parse to? ask Xavier?
    In fact, it is almost certainly wrong, and implementation-dependent. *)

Variable atomic_int : type.
(* Variable is_atomic_version : type -> type -> Prop.
   Variable _Atomic : type -> type. *)
Variable atomic_int_at : share -> val -> val -> mpred.
Hypothesis atomic_int_at__ : forall sh v p, atomic_int_at sh v p |-- atomic_int_at sh Vundef p.
(*Variable atom_ptr_at : share -> val -> val -> mpred.*)

Definition make_atomic_spec :=
  WITH v : val
  PRE [ 1%positive OF tint ]
    PROP ()
    LOCAL (temp 1%positive v)
    SEP ()
  POST [ tptr atomic_int ]
   EX p : val,
    PROP ()
    LOCAL (temp ret_temp p)
    SEP (atomic_int_at Ews v p).

Definition AL_type := ProdType (ProdType (ProdType (ProdType (ConstType val)
  (ConstType coPset)) (ConstType coPset))
  (ArrowType (ConstType val) Mpred)) (ConstType invG).

Program Definition atomic_load_spec := TYPE AL_type
  WITH p : val, Eo : coPset, Ei : coPset, Q : val -> mpred, inv_names : invG
  PRE [ 1%positive OF tptr atomic_int ]
   PROP (subseteq Ei Eo)
   LOCAL (temp 1%positive p)
   SEP (|={Eo,Ei}=> EX sh : share, EX v : val, !!(readable_share sh) &&
              atomic_int_at sh v p * (atomic_int_at sh v p -* |={Ei,Eo}=> Q v))%I
  POST [ tint ]
   EX v : val,
   PROP ()
   LOCAL (temp ret_temp v)
   SEP (Q v).
Next Obligation.
Proof.
  repeat intro.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal;
    f_equal; rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  setoid_rewrite fupd_nonexpansive; do 2 f_equal.
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

Definition AS_type := ProdType (ProdType (ProdType (ProdType (ConstType (val * val))
  (ConstType coPset)) (ConstType coPset)) Mpred) (ConstType invG).

Program Definition atomic_store_spec := TYPE AS_type
  WITH p : val, v : val, Eo : coPset, Ei : coPset, Q : mpred, inv_names : invG
  PRE [ 1%positive OF tptr atomic_int, 2%positive OF tint ]
   PROP (subseteq Ei Eo)
   LOCAL (temp 1%positive p; temp 2%positive v)
   SEP (|={Eo,Ei}=> EX sh : share, !!(writable_share sh) && atomic_int_at sh Vundef p *
      (atomic_int_at sh v p -* |={Ei,Eo}=> Q))%I
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (Q).
Next Obligation.
Proof.
  repeat intro.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal;
    f_equal; rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
  setoid_rewrite fupd_nonexpansive; do 2 f_equal.
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

Definition ACAS_type := ProdType (ProdType (ProdType (ProdType (ConstType (val * share * val * val * val))
  (ConstType coPset)) (ConstType coPset))
  (ArrowType (ConstType val) Mpred)) (ConstType invG).

Program Definition atomic_CAS_spec := TYPE ACAS_type
  WITH p : val, shc : share, pc : val, c : val, v : val, Eo : coPset, Ei : coPset, Q : val -> mpred, inv_names : invG
  PRE [ 1%positive OF tptr atomic_int, 2%positive OF tptr tint, 3%positive OF tint ]
   PROP (readable_share shc; subseteq Ei Eo)
   LOCAL (temp 1%positive p; temp 2%positive pc; temp 3%positive v)
   SEP (data_at shc tint c pc; |={Eo,Ei}=> EX sh : share, EX v0 : val,
      !!(writable_share sh) && atomic_int_at sh v0 p *
           (atomic_int_at sh (if eq_dec v0 c then v else v0) p -* |={Ei,Eo}=> Q v0))%I
  POST [ tint ]
   EX v' : val,
   PROP ()
   LOCAL (temp ret_temp (vint (if eq_dec v' c then 1 else 0)))
   SEP (data_at shc tint c pc; Q v').
Next Obligation.
Proof.
  repeat intro.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal;
    f_equal; rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
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

Definition AEX_type := ProdType (ProdType (ProdType (ProdType (ConstType (val * val))
  (ConstType coPset)) (ConstType coPset))
  (ArrowType (ConstType val) Mpred)) (ConstType invG).

Program Definition atomic_exchange_spec := TYPE AEX_type
  WITH p : val, v : val, Eo : coPset, Ei : coPset, Q : val -> mpred, inv_names : invG
  PRE [ 1%positive OF tptr tint, 2%positive OF tint ]
   PROP (subseteq Ei Eo)
   LOCAL (temp 1%positive p; temp 2%positive v)
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
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal;
    f_equal; rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
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
Definition ALI_type := ProdType (ProdType (ProdType (ProdType (ConstType val)
  (ConstType coPset)) (ConstType coPset))
  (ArrowType (ConstType Z) Mpred)) (ConstType invG).

Program Definition atomic_load_int_spec := TYPE ALI_type
  WITH p : val, Eo : coPset, Ei : coPset, Q : Z -> mpred, inv_names : invG
  PRE [ 1%positive OF tptr atomic_int ]
   PROP (subseteq Ei Eo)
   LOCAL (temp 1%positive p)
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
  setoid_rewrite fupd_nonexpansive; do 2 f_equal.
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
  apply subsume_subsume.
  split; auto; split; auto; intros; simpl in *.
  destruct x2 as ((((p, Eo), Ei), Q), inv_names).
  intros; match goal with |- ?P |-- |==> ?Q => change (P |-- |==> Q)%I end.
  intros; iIntros "[_ H] !>".
  iExists nil, (p, Eo, Ei, fun v => match v with Vint i => Q (Int.signed i) | _ => FF end, inv_names), emp.
  rewrite emp_sepcon; iSplit.
  - unfold PROPx, LOCALx, SEPx; simpl.
    iDestruct "H" as "($ & $ & H & _)"; rewrite sepcon_emp.
    iMod "H"; iModIntro.
    iDestruct "H" as (sh v) "[[% H1] H2]".
    destruct H.
    iExists sh, (vint v); iFrame.
    rewrite Int.signed_repr; auto.
  - iPureIntro.
    intros; match goal with |- ?P |-- |==> ?Q => change (P |-- |==> Q)%I end.
    iIntros "(_ & _ & H) !>".
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

Definition ASI_type := ProdType (ProdType (ProdType (ProdType (ConstType (val * Z))
  (ConstType coPset)) (ConstType coPset)) Mpred) (ConstType invG).

Program Definition atomic_store_int_spec := TYPE ASI_type
  WITH p : val, v : Z, Eo : coPset, Ei : coPset, Q : mpred, inv_names : invG
  PRE [ 1%positive OF tptr atomic_int, 2%positive OF tint ]
   PROP (repable_signed v; subseteq Ei Eo)
   LOCAL (temp 1%positive p; temp 2%positive (vint v))
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
  setoid_rewrite fupd_nonexpansive; do 2 f_equal.
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
  apply subsume_subsume.
  split; auto; split; auto; intros; simpl in *.
  destruct x2 as (((((p, v), Eo), Ei), Q), inv_names).
  intros; match goal with |- ?P |-- |==> ?Q => change (P |-- |==> Q)%I end.
  intros; iIntros "[_ H] !>".
  iExists nil, (p, vint v, Eo, Ei, Q, inv_names), emp.
  rewrite emp_sepcon; iSplit.
  - unfold PROPx, LOCALx, SEPx; simpl.
    iDestruct "H" as "(% & $ & H & _)"; rewrite sepcon_emp.
    destruct H; auto.
  - iPureIntro.
    intros; match goal with |- ?P |-- |==> ?Q => change (P |-- |==> Q)%I end.
    by iIntros "(_ & _ & $)".
Qed.

Definition ACASI_type := ProdType (ProdType (ProdType (ProdType (ConstType (val * share * val * Z * Z))
  (ConstType coPset)) (ConstType coPset))
  (ArrowType (ConstType Z) Mpred)) (ConstType invG).

Program Definition atomic_CAS_int_spec := TYPE ACASI_type
  WITH p : val, shc : share, pc : val, c : Z, v : Z, Eo : coPset, Ei : coPset, Q : Z -> mpred, inv_names : invG
  PRE [ 1%positive OF tptr atomic_int, 2%positive OF tptr tint, 3%positive OF tint ]
   PROP (repable_signed c; repable_signed v; readable_share shc; subseteq Ei Eo)
   LOCAL (temp 1%positive p; temp 2%positive pc; temp 3%positive (vint v))
   SEP (data_at shc tint (vint c) pc; |={Eo,Ei}=> EX sh : share, EX v0 : Z,
      !!(writable_share sh /\ repable_signed v0) && atomic_int_at sh (vint v0) p *
           (atomic_int_at sh (vint (if eq_dec v0 c then v else v0)) p -* |={Ei,Eo}=> Q v0))%I
  POST [ tint ]
   EX v' : Z,
   PROP (repable_signed v')
   LOCAL (temp ret_temp (vint (if eq_dec v' c then 1 else 0)))
   SEP (data_at shc tint (vint c) pc; Q v').
Next Obligation.
Proof.
  repeat intro.
  unfold PROPx, LOCALx, SEPx; simpl; rewrite !approx_andp; f_equal;
    f_equal; rewrite -> !sepcon_emp, ?approx_sepcon, ?approx_idem.
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

Lemma atomic_CAS_int : funspec_sub atomic_CAS_spec atomic_CAS_int_spec.
Proof.
  apply subsume_subsume.
  split; auto; split; auto; intros; simpl in *.
  destruct x2 as ((((((((p, shc), pc), c), v), Eo), Ei), Q), inv_names).
  intros; match goal with |- ?P |-- |==> ?Q => change (P |-- |==> Q)%I end.
  intros; iIntros "[_ H] !>".
  iExists nil, (p, shc, pc, vint c, vint v, Eo, Ei, fun v => match v with Vint i => Q (Int.signed i) | _ => FF end, inv_names), emp.
  rewrite emp_sepcon; iSplit.
  - unfold PROPx, LOCALx, SEPx; simpl.
    iDestruct "H" as "(% & $ & $ & H & _)"; rewrite sepcon_emp.
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
    intros; match goal with |- ?P |-- |==> ?Q => change (P |-- |==> Q)%I end.
    iIntros "(_ & _ & H) !>".
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
    rewrite sepcon_emp; iFrame.
Qed.

Definition AEXI_type := ProdType (ProdType (ProdType (ProdType (ConstType (val * Z))
  (ConstType coPset)) (ConstType coPset))
  (ArrowType (ConstType Z) Mpred)) (ConstType invG).

Program Definition atomic_exchange_int_spec := TYPE AEXI_type
  WITH p : val, v : Z, Eo : coPset, Ei : coPset, Q : Z -> mpred, inv_names : invG
  PRE [ 1%positive OF tptr tint, 2%positive OF tint ]
   PROP (repable_signed v; subseteq Ei Eo)
   LOCAL (temp 1%positive p; temp 2%positive (vint v))
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

Lemma atomic_exchange_int : funspec_sub atomic_exchange_spec atomic_exchange_int_spec.
Proof.
  apply subsume_subsume.
  split; auto; split; auto; intros; simpl in *.
  destruct x2 as (((((p, v), Eo), Ei), Q), inv_names).
  intros; match goal with |- ?P |-- |==> ?Q => change (P |-- |==> Q)%I end.
  intros; iIntros "[_ H] !>".
  iExists nil, (p, vint v, Eo, Ei, fun v => match v with Vint i => Q (Int.signed i) | _ => FF end, inv_names), emp.
  rewrite emp_sepcon; iSplit.
  - unfold PROPx, LOCALx, SEPx; simpl.
    iDestruct "H" as "(% & $ & H & _)"; rewrite sepcon_emp.
    destruct H; iSplit; auto.
    iMod "H"; iModIntro.
    iDestruct "H" as (sh v0) "[[% H1] H2]".
    destruct H1.
    iExists sh, (vint v0); iFrame.
    rewrite -> Int.signed_repr; auto.
  - unfold PROPx, LOCALx, SEPx; simpl.
    iPureIntro.
    intros; match goal with |- ?P |-- |==> ?Q => change (P |-- |==> Q)%I end.
    iIntros "(_ & _ & H) !>".
    iDestruct "H" as (r) "(_ & % & Q & _)".
    destruct H, r; try done.
    iExists (Int.signed i); iSplit; auto.
    { iPureIntro; split; auto.
      apply Int.signed_range. }
    iSplit; [iSplit; auto|].
    { rewrite Int.repr_signed; auto. }
    rewrite sepcon_emp; iFrame.
Qed.

End SC_atomics.
