Require Import VST.floyd.proofauto.
Require Import VST.progs.stackframe_demo.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition iden_spec :=
 DECLARE _iden
  WITH x : Z
  PRE  [ tint ]
     PROP () PARAMS (Vint (Int.repr x)) SEP ()
  POST [ tint ]
     PROP () RETURN (Vint (Int.repr x)) SEP ().

Definition Gprog : funspecs :=
         ltac:(with_library prog [ iden_spec ]).

Lemma body_iden: semax_body Vprog Gprog f_iden iden_spec.
Proof.
  start_function.
  forward.
  forward.
  forward.
  forward.
  entailer!.
Qed.

Lemma body_iden': semax_body Vprog Gprog f_iden iden_spec.
Proof.
  start_function.
  forward.
  forward.
  forward.
  apply semax_pre with
      (PROP ( )
       LOCAL (temp _t'1 (Vint (Int.repr x)); temp _p v_y; temp _x (Vint (Int.repr x)))
       SEP (data_at Tsh tint (Vint (Int.repr x)) v_y)).
  (* Drop lvar in LOCAL *)
  { entailer!. }
  Fail forward.
  (* Should it fail? Yes. Because the lvar clause are used in stackframe cancel.
     The error message? We'd Better improve it.  --- Qinxiang 2019.11.8 *)
Abort.

