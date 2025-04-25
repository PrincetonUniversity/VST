Require Import VST.floyd.proofauto.
Require Import VST.floyd.compat. Import NoOracle.
Require Import triang.
Require Import simple_spec_stdlib.
Require Import PileModel.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

(*APD is empty, but the ASI still depend n the MallocFree-APD*)


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

Definition TriangASI:funspecs := [Triang_nth_spec].

