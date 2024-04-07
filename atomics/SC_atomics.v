(* Hoare rules for SC atomics *)
Require Import VST.concurrency.conclib.
Require Import VST.floyd.library.
Require Import VST.zlist.sublist.

(* Warning: it is UNSOUND to use both this file and acq_rel_atomics.v in the same proof! There is
   not yet an operational model that can validate the use of both SC and RA atomics. *)

(* At present, due to complexities in the specifications of the C11 atomics (generics, _Atomic types, etc.), these are specs for wrapper functions for common cases.
   There's probably a more systematic approach possible. *)

Section SC_atomics.

Context `{!VSTGS OK_ty Σ}.

Class atomic_int_impl (atomic_int : type) := { atomic_int_at : share -> val -> val -> mpred;
  atomic_int_at__ : forall sh v p, atomic_int_at sh v p ⊢ atomic_int_at sh Vundef p;
  atomic_int_conflict : forall sh v v' p, sepalg.nonidentity sh -> atomic_int_at sh v p ∗ atomic_int_at sh v' p ⊢ False }.

Class atomic_ptr_impl := { atomic_ptr : type; atomic_ptr_at : share -> val -> val -> mpred;
  atomic_ptr_conflict : forall sh v v' p, sepalg.nonidentity sh -> atomic_ptr_at sh v p ∗ atomic_ptr_at sh v' p ⊢ False }.

Context {CS : compspecs} `{AI : atomic_int_impl} {AP : atomic_ptr_impl}.

Definition make_atomic_spec :=
  WITH v : val
  PRE [ tint ]
    PROP ()
    PARAMS (v)
    SEP ()
  POST [ tptr atomic_int ]
   ∃ p : val,
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
   ∃ p : val,
    PROP (is_pointer_or_null p)
    RETURN (p)
    SEP (atomic_ptr_at Ews v p).

Definition free_atomic_ptr_spec :=
  WITH p : val
  PRE [ tptr atomic_ptr ]
    PROP (is_pointer_or_null p)
    PARAMS (p)
    SEP (∃ v : val, atomic_ptr_at Ews v p)
  POST[ tvoid ]
    PROP ()
    LOCAL ()
    SEP ().

Definition free_atomic_int_spec :=
  WITH p : val
  PRE [ tptr atomic_int ]
    PROP (is_pointer_or_null p)
    PARAMS (p)
    SEP (∃ v : val, atomic_int_at Ews v p)
  POST[ tvoid ]
    PROP ()
    LOCAL ()
    SEP ().

Definition AL_type := ProdType (ProdType (ProdType (ConstType val)
  (ConstType coPset)) (ConstType coPset))
  (DiscreteFunType val Mpred).

Program Definition atomic_load_spec := TYPE AL_type
  WITH p : val, Eo : coPset, Ei : coPset, Q : val -> mpred
  PRE [ tptr atomic_int ]
   PROP (subseteq Ei Eo)
   PARAMS (p)
   SEP (|={Eo,Ei}=> ∃ sh : share, ∃ v : val, ⌜readable_share sh⌝ ∧
              atomic_int_at sh v p ∗ (atomic_int_at sh v p -∗ |={Ei,Eo}=> Q v))
  POST [ tint ]
   ∃ v : val,
   PROP ()
   RETURN (v)
   SEP (Q v).
Next Obligation.
Proof.
  intros ? (((?, ?), ?), ?) (((?, ?), ?), ?) ((([=] & [=]) & [=]) & HQ) ?; simpl in *; subst.
  repeat f_equiv.
Qed.
Next Obligation.
  intros ? (((?, ?), ?), ?) (((?, ?), ?), ?) ((([=] & [=]) & [=]) & HQ) ?; simpl in *; subst.
  repeat f_equiv.
Qed.

Definition AS_type := ProdType (ProdType (ProdType (ConstType (val * val))
  (ConstType coPset)) (ConstType coPset)) Mpred.

Program Definition atomic_store_spec := TYPE AS_type
  WITH p : val, v : val, Eo : coPset, Ei : coPset, Q : mpred
  PRE [ tptr atomic_int, tint ]
   PROP (subseteq Ei Eo)
   PARAMS (p; v)
   SEP (|={Eo,Ei}=> ∃ sh : share, ⌜writable_share sh⌝ ∧ atomic_int_at sh Vundef p ∗
      (atomic_int_at sh v p -∗ |={Ei,Eo}=> Q))
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (Q).
Next Obligation.
Proof.
  intros ? ((((?, ?), ?), ?), ?) ((((?, ?), ?), ?), ?) ((([=] & [=]) & [=]) & HQ) ?; simpl in *; subst.
  by repeat f_equiv.
Qed.
Next Obligation.
  intros ? ((((?, ?), ?), ?), ?) ((((?, ?), ?), ?), ?) ((([=] & [=]) & [=]) & HQ) ?; simpl in *; subst.
  by repeat f_equiv.
Qed.

Definition ACAS_type := ProdType (ProdType (ProdType (ConstType (val * share * val * val * val))
  (ConstType coPset)) (ConstType coPset))
  (DiscreteFunType val Mpred).

Program Definition atomic_CAS_spec := TYPE ACAS_type
  WITH p : val, shc : share, pc : val, c : val, v : val, Eo : coPset, Ei : coPset, Q : val -> mpred
  PRE [ tptr atomic_int, tptr tint, tint ]
   PROP (readable_share shc; subseteq Ei Eo)
   PARAMS (p; pc; v)
   SEP (data_at shc tint c pc; |={Eo,Ei}=> ∃ sh : share, ∃ v0 : val,
      ⌜writable_share sh⌝ ∧ atomic_int_at sh v0 p ∗
           (atomic_int_at sh (if eq_dec v0 c then v else v0) p -∗ |={Ei,Eo}=> Q v0))
  POST [ tint ]
   ∃ v' : val,
   PROP ()
   LOCAL (temp ret_temp (vint (if eq_dec v' c then 1 else 0)))
   SEP (data_at shc tint v' pc; Q v').
Next Obligation.
Proof.
  intros ? (((((((?, ?), ?), ?), ?), ?), ?), ?) ((((?, ?), ?), ?), ?) ((([=] & [=]) & [=]) & HQ) ?; simpl in *; subst.
  by repeat f_equiv.
Qed.
Next Obligation.
  intros ? (((((((?, ?), ?), ?), ?), ?), ?), ?) ((((?, ?), ?), ?), ?) ((([=] & [=]) & [=]) & HQ) ?; simpl in *; subst.
  by repeat f_equiv.
Qed.

Definition AEX_type := ProdType (ProdType (ProdType (ConstType (val * val))
  (ConstType coPset)) (ConstType coPset))
  (DiscreteFunType val Mpred).

Program Definition atomic_exchange_spec := TYPE AEX_type
  WITH p : val, v : val, Eo : coPset, Ei : coPset, Q : val -> mpred
  PRE [ tptr atomic_int, tint ]
   PROP (subseteq Ei Eo)
   PARAMS (p; v)
   SEP (|={Eo,Ei}=> ∃ sh : share, ∃ v0 : val, ⌜writable_share sh⌝ ∧
              atomic_int_at sh v0 p ∗
        (atomic_int_at sh v p -∗ |={Ei,Eo}=> Q v0))
  POST [ tint ]
   ∃ v' : int,
   PROP ()
   LOCAL (temp ret_temp (Vint v'))
   SEP (Q (Vint v')).
Next Obligation.
Proof.
  intros ? ((((?, ?), ?), ?), ?) ((((?, ?), ?), ?), ?) ((([=] & [=]) & [=]) & HQ) ?; simpl in *; subst.
  by repeat f_equiv.
Qed.
Next Obligation.
  intros ? ((((?, ?), ?), ?), ?) ((((?, ?), ?), ?), ?) ((([=] & [=]) & [=]) & HQ) ?; simpl in *; subst.
  by repeat f_equiv.
Qed.

(* subspecs for integer operations *)
Definition ALI_type := ProdType (ProdType (ProdType (ConstType val)
  (ConstType coPset)) (ConstType coPset))
  (DiscreteFunType Z Mpred).

Program Definition atomic_load_int_spec := TYPE ALI_type
  WITH p : val, Eo : coPset, Ei : coPset, Q : Z -> mpred
  PRE [ tptr atomic_int ]
   PROP (subseteq Ei Eo)
   PARAMS (p)
   SEP (|={Eo,Ei}=> ∃ sh : share, ∃ v : Z, ⌜readable_share sh /\ repable_signed v⌝ ∧
              atomic_int_at sh (vint v) p ∗ (atomic_int_at sh (vint v) p -∗ |={Ei,Eo}=> Q v))
  POST [ tint ]
   ∃ v : Z,
   PROP (repable_signed v)
   LOCAL (temp ret_temp (vint v))
   SEP (Q v).
Next Obligation.
Proof.
  intros ? (((?, ?), ?), ?) (((?, ?), ?), ?) ((([=] & [=]) & [=]) & HQ) ?; simpl in *; subst.
  by repeat f_equiv.
Qed.
Next Obligation.
  intros ? (((?, ?), ?), ?) (((?, ?), ?), ?) ((([=] & [=]) & [=]) & HQ) ?; simpl in *; subst.
  by repeat f_equiv.
Qed.

Lemma atomic_load_int : funspec_sub atomic_load_spec atomic_load_int_spec.
Proof.
  split; first done; intros; simpl in *.
  destruct x2 as (((p, Eo), Ei), Q).
  intros; iIntros "[_ H] !>".
  iExists (p, Eo, Ei, fun v => match v with Vint i => Q (Int.signed i) | _ => False end), emp.
  iSplit; first done.
  iSplit.
  - iSplit; first done.
    unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx, argsassert2assert; simpl.
    monPred.unseal.
    iDestruct "H" as "($ & $ & $ & H & $)".
    iMod "H"; iModIntro.
    iDestruct "H" as (sh v) "((% & %) & ? & ?)".
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
    iSplit; [iSplit|]; auto.
    rewrite Int.repr_signed; auto.
Qed.

Definition ASI_type := ProdType (ProdType (ProdType (ConstType (val * Z))
  (ConstType coPset)) (ConstType coPset)) Mpred.

Program Definition atomic_store_int_spec := TYPE ASI_type
  WITH p : val, v : Z, Eo : coPset, Ei : coPset, Q : mpred
  PRE [ tptr atomic_int, tint ]
   PROP (repable_signed v; subseteq Ei Eo)
   PARAMS (p; vint v)
   SEP (|={Eo,Ei}=> ∃ sh : share, ⌜writable_share sh⌝ ∧ atomic_int_at sh Vundef p ∗
      (atomic_int_at sh (vint v) p -∗ |={Ei,Eo}=> Q))
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (Q).
Next Obligation.
Proof.
  intros ? ((((?, ?), ?), ?), ?) ((((?, ?), ?), ?), ?) ((([=] & [=]) & [=]) & HQ) ?; simpl in *; subst.
  by repeat f_equiv.
Qed.
Next Obligation.
  intros ? ((((?, ?), ?), ?), ?) ((((?, ?), ?), ?), ?) ((([=] & [=]) & [=]) & HQ) ?; simpl in *; subst.
  by repeat f_equiv.
Qed.

Lemma atomic_store_int : funspec_sub atomic_store_spec atomic_store_int_spec.
Proof.
  split; first done; intros; simpl in *.
  destruct x2 as ((((p, v), Eo), Ei), Q).
  intros; iIntros "[_ H] !>".
  iExists (p, vint v, Eo, Ei, Q), emp.
  iSplit; first done.
  iSplit.
  - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx; simpl.
    monPred.unseal.
    iDestruct "H" as "(% & $ & $ & H & $)".
    destruct H; auto.
  - iPureIntro.
    by iIntros (?) "(_ & _ & $)".
Qed.

Definition ACASI_type := ProdType (ProdType (ProdType (ConstType (val * share * val * Z * Z))
  (ConstType coPset)) (ConstType coPset))
  (DiscreteFunType Z Mpred).

Program Definition atomic_CAS_int_spec := TYPE ACASI_type
  WITH p : val, shc : share, pc : val, c : Z, v : Z, Eo : coPset, Ei : coPset, Q : Z -> mpred
  PRE [ tptr atomic_int, tptr tint, tint ]
   PROP (repable_signed c; repable_signed v; readable_share shc; subseteq Ei Eo)
   PARAMS (p; pc; vint v)
   SEP (data_at shc tint (vint c) pc; |={Eo,Ei}=> ∃ sh : share, ∃ v0 : Z,
      ⌜writable_share sh /\ repable_signed v0⌝ ∧ atomic_int_at sh (vint v0) p ∗
           (atomic_int_at sh (vint (if eq_dec v0 c then v else v0)) p -∗ |={Ei,Eo}=> Q v0))
  POST [ tint ]
   ∃ v' : Z,
   PROP (repable_signed v')
   LOCAL (temp ret_temp (vint (if eq_dec v' c then 1 else 0)))
   SEP (data_at shc tint (vint v') pc; Q v').
Next Obligation.
Proof.
  intros ? (((((((?, ?), ?), ?), ?), ?), ?), ?) ((((?, ?), ?), ?), ?) ((([=] & [=]) & [=]) & HQ) ?; simpl in *; subst.
  by repeat f_equiv.
Qed.
Next Obligation.
  intros ? (((((((?, ?), ?), ?), ?), ?), ?), ?) ((((?, ?), ?), ?), ?) ((([=] & [=]) & [=]) & HQ) ?; simpl in *; subst.
  by repeat f_equiv.
Qed.

Lemma atomic_CAS_int : funspec_sub atomic_CAS_spec atomic_CAS_int_spec.
Proof.
  split; first done; intros; simpl in *.
  destruct x2 as (((((((p, shc), pc), c), v), Eo), Ei), Q).
  intros; iIntros "[_ H] !>".
  iExists (p, shc, pc, vint c, vint v, Eo, Ei, fun v => match v with Vint i => Q (Int.signed i) | _ => False end), emp.
  iSplit; first done.
  iSplit.
  - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx; simpl; monPred.unseal.
    iDestruct "H" as "(% & $ & $ & $ & H & $)".
    destruct H as (? & ? & ?); iSplit; auto.
    iMod "H"; iModIntro.
    iDestruct "H" as (sh v0) "((% & %) & ? & ?)".
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
    rewrite Int.repr_signed; iFrame.
Qed.

Definition AEXI_type := ProdType (ProdType (ProdType (ConstType (val * Z))
  (ConstType coPset)) (ConstType coPset))
  (DiscreteFunType Z Mpred).

Program Definition atomic_exchange_int_spec := TYPE AEXI_type
  WITH p : val, v : Z, Eo : coPset, Ei : coPset, Q : Z -> mpred
  PRE [ tptr atomic_int, tint ]
   PROP (repable_signed v; subseteq Ei Eo)
   PARAMS (p; vint v)
   SEP (|={Eo,Ei}=> ∃ sh : share, ∃ v0 : Z, ⌜writable_share sh /\ repable_signed v0⌝ ∧
              atomic_int_at sh (vint v0) p ∗
        (atomic_int_at sh (vint v) p -∗ |={Ei,Eo}=> Q v0))
  POST [ tint ]
   ∃ v' : Z,
   PROP (repable_signed v')
   LOCAL (temp ret_temp (vint v'))
   SEP (Q v').
Next Obligation.
Proof.
  intros ? ((((?, ?), ?), ?), ?) ((((?, ?), ?), ?), ?) ((([=] & [=]) & [=]) & HQ) ?; simpl in *; subst.
  by repeat f_equiv.
Qed.
Next Obligation.
  intros ? ((((?, ?), ?), ?), ?) ((((?, ?), ?), ?), ?) ((([=] & [=]) & [=]) & HQ) ?; simpl in *; subst.
  by repeat f_equiv.
Qed.

Lemma atomic_exchange_int : funspec_sub atomic_exchange_spec atomic_exchange_int_spec.
Proof.
  split; first done; intros; simpl in *.
  destruct x2 as ((((p, v), Eo), Ei), Q).
  intros; iIntros "[_ H] !>".
  iExists (p, vint v, Eo, Ei, fun v => match v with Vint i => Q (Int.signed i) | _ => False end), emp.
  iSplit; first done.
  iSplit.
  - unfold PROPx, PARAMSx, GLOBALSx, LOCALx, SEPx; simpl; monPred.unseal.
    iDestruct "H" as "(% & $ & $ & H & $)".
    destruct H; iSplit; auto.
    iMod "H"; iModIntro.
    iDestruct "H" as (sh v0) "((% & %) & ? & ?)".
    iExists sh, (vint v0); iFrame.
    rewrite -> Int.signed_repr; auto.
  - unfold PROPx, LOCALx, SEPx; simpl.
    iPureIntro.
    iIntros (?) "(_ & _ & H)".
    iDestruct "H" as (r) "(_ & % & Q & _)".
    destruct H; try done.
    monPred.unseal.
    iExists (Int.signed r); iSplit; auto.
    { iPureIntro; split; auto.
      apply Int.signed_range. }
    iSplit; [iSplit; auto|].
    { rewrite Int.repr_signed; auto. }
    iFrame.
Qed.

(* specs for pointer operations *)

Definition ALI_ptr_type := ProdType (ProdType (ProdType (ConstType val)
  (ConstType coPset)) (ConstType coPset))
  (DiscreteFunType val Mpred).

Program Definition atomic_load_ptr_spec := TYPE ALI_ptr_type
  WITH p : val, Eo : coPset, Ei : coPset, Q : val -> mpred
  PRE [ tptr atomic_ptr ]
   PROP (subseteq Ei Eo)
   PARAMS (p)
   SEP (|={Eo,Ei}=> ∃ sh : share, ∃ v : val, ⌜readable_share sh⌝ ∧
              atomic_ptr_at sh v p ∗ (atomic_ptr_at sh v p -∗ |={Ei,Eo}=> Q v))
  POST [ tptr Tvoid ]
   ∃ v : val,
   PROP ()
   LOCAL (temp ret_temp v)
   SEP (Q v).
Next Obligation.
Proof.
  intros ? (((?, ?), ?), ?) (((?, ?), ?), ?) ((([=] & [=]) & [=]) & HQ) ?; simpl in *; subst.
  by repeat f_equiv.
Qed.
Next Obligation.
  intros ? (((?, ?), ?), ?) (((?, ?), ?), ?) ((([=] & [=]) & [=]) & HQ) ?; simpl in *; subst.
  by repeat f_equiv.
Qed.

Definition ASI_ptr_type := ProdType (ProdType (ProdType (ConstType (val * val))
  (ConstType coPset)) (ConstType coPset)) Mpred.

Program Definition atomic_store_ptr_spec := TYPE ASI_ptr_type
  WITH p : val, v : val, Eo : coPset, Ei : coPset, Q : mpred
  PRE [ tptr atomic_ptr, tptr Tvoid ]
   PROP (subseteq Ei Eo)
   PARAMS (p; v)
   SEP (|={Eo,Ei}=> ∃ sh : share, ⌜writable_share sh⌝ ∧ atomic_ptr_at sh Vundef p ∗
      (atomic_ptr_at sh v p -∗ |={Ei,Eo}=> Q))
  POST [ tvoid ]
   PROP ()
   LOCAL ()
   SEP (Q).
Next Obligation.
Proof.
  intros ? ((((?, ?), ?), ?), ?) ((((?, ?), ?), ?), ?) ((([=] & [=]) & [=]) & HQ) ?; simpl in *; subst.
  by repeat f_equiv.
Qed.
Next Obligation.
  intros ? ((((?, ?), ?), ?), ?) ((((?, ?), ?), ?), ?) ((([=] & [=]) & [=]) & HQ) ?; simpl in *; subst.
  by repeat f_equiv.
Qed.

Definition ACASI_ptr_type := ProdType (ProdType (ProdType (ConstType (val * share * val * val * val))
  (ConstType coPset)) (ConstType coPset))
  (DiscreteFunType val Mpred).

Program Definition atomic_CAS_ptr_spec := TYPE ACASI_ptr_type
  WITH p : val, shc : share, pc : val, c : val, v : val, Eo : coPset, Ei : coPset, Q : val -> mpred
  PRE [ tptr atomic_ptr, tptr (tptr Tvoid), tptr Tvoid ]
   PROP (readable_share shc; subseteq Ei Eo)
   PARAMS (p; pc; v)
   SEP (data_at shc (tptr Tvoid) c pc; |={Eo,Ei}=> ∃ sh : share, ∃ v0 : val,
      ⌜writable_share sh⌝ ∧ atomic_ptr_at sh v0 p ∗
           (atomic_ptr_at sh (if eq_dec v0 c then v else v0) p -∗ |={Ei,Eo}=> Q v0))
  POST [ tint ]
   ∃ v' : val,
   PROP ()
   LOCAL (temp ret_temp (vint (if eq_dec v' c then 1 else 0)))
   SEP (data_at shc (tptr Tvoid) c pc; Q v').
Next Obligation.
Proof.
  intros ? (((((((?, ?), ?), ?), ?), ?), ?), ?) ((((?, ?), ?), ?), ?) ((([=] & [=]) & [=]) & HQ) ?; simpl in *; subst.
  by repeat f_equiv.
Qed.
Next Obligation.
  intros ? (((((((?, ?), ?), ?), ?), ?), ?), ?) ((((?, ?), ?), ?), ?) ((([=] & [=]) & [=]) & HQ) ?; simpl in *; subst.
  by repeat f_equiv.
Qed.

Definition AEXI_ptr_type := ProdType (ProdType (ProdType (ConstType (val * val))
  (ConstType coPset)) (ConstType coPset))
  (DiscreteFunType val Mpred).

Program Definition atomic_exchange_ptr_spec := TYPE AEXI_ptr_type
  WITH p : val, v : val, Eo : coPset, Ei : coPset, Q : val -> mpred
  PRE [ tptr atomic_ptr, tptr Tvoid ]
   PROP (subseteq Ei Eo)
   PARAMS (p; v)
   SEP (|={Eo,Ei}=> ∃ sh : share, ∃ v0 : val, ⌜writable_share sh⌝ ∧
              atomic_ptr_at sh v0 p ∗
        (atomic_ptr_at sh v p -∗ |={Ei,Eo}=> Q v0))
  POST [ tint ]
   ∃ v' : val,
   PROP ()
   LOCAL (temp ret_temp v')
   SEP (Q v').
Next Obligation.
Proof.
  intros ? ((((?, ?), ?), ?), ?) ((((?, ?), ?), ?), ?) ((([=] & [=]) & [=]) & HQ) ?; simpl in *; subst.
  by repeat f_equiv.
Qed.
Next Obligation.
  intros ? ((((?, ?), ?), ?), ?) ((((?, ?), ?), ?), ?) ((([=] & [=]) & [=]) & HQ) ?; simpl in *; subst.
  by repeat f_equiv.
Qed.

End SC_atomics.
