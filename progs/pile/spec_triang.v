Require Import VST.floyd.proofauto.
Require Import triang.
Require Import spec_stdlib.
Require Import spec_pile.
Global Open Scope funspec_scope.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.


Local Open Scope assert.

Fixpoint triang (n: nat) :=
 match n with
 | O => 0
 | S n' => Z.of_nat n + triang n'
 end.

Definition Triang_nth_spec :=
 DECLARE _Triang_nth
 WITH n:Z, gv: globals
 PRE [ tint ] 
    PROP( 0 <= n < 1000) 
    PARAMS (Vint (Int.repr n)) GLOBALS (gv) 
    SEP(mem_mgr gv)
 POST[ tint ]
    PROP()
    LOCAL(temp ret_temp (Vint (Int.repr (triang (Z.to_nat n)))))
    SEP(mem_mgr gv).

Definition specs := [Triang_nth_spec].
