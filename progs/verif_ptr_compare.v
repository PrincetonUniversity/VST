Require Import VST.floyd.proofauto.
Require Import VST.progs.ptr_compare.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

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

Definition Gprog : funspecs := nil.

Lemma body_f: semax_body Vprog Gprog f_f f_spec.
Proof.
start_function.
(* AT THIS POINT, "forward" will entirely solve the goal.
  The method shown here is
  only to illustrate some of the steps that "forward" takes.
*)
eapply semax_return_Some.
+ entailer_for_return.
+ entailer_for_return.
+ solve_return_outer_gen.
+ solve_canon_derives_stackframe.
+ unfold POSTCONDITION, abbreviate; solve_return_inner_gen.
+ entailer_for_return.
Qed.

(* TODO:  Put some more examples in the .c file! *)

