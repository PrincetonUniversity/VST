Require Import floyd.proofauto.
Require Import progs.ptr_compare.

Instance CompSpecs : compspecs.
Proof. make_compspecs prog. Defined.

Local Open Scope logic.

Definition f_spec :=
 DECLARE _f
  WITH p: val, q:val, sh: share
  PRE  [_p OF tptr tint, _q OF tptr tint] 
        PROP (sepalg.nonidentity sh)
        LOCAL(temp _p p; temp _q q)
        SEP(data_at sh tint (Vint Int.zero) p; data_at sh tint (Vint Int.zero) q)
  POST [ tint ]
         PROP() 
         LOCAL (temp 1%positive (Vint (if eq_dec p q then Int.one else Int.zero)))
         SEP (data_at sh tint (Vint Int.zero) p; data_at sh tint (Vint Int.zero) q).

Definition Vprog : varspecs := nil.

Definition Gprog : funspecs := nil.

Lemma body_f: semax_body Vprog Gprog f_f f_spec.
Proof.
start_function.
name p' _p.
name q' _q.
forward.
entailer!.
Qed.
